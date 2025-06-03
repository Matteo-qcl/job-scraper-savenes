import requests
import json
from geopy.geocoders import Nominatim
from geopy.distance import geodesic
import time
from datetime import datetime, timedelta
import os
from dotenv import load_dotenv
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import sqlite3
import schedule
import threading
import logging
from logging.handlers import RotatingFileHandler
import pytz
from bs4 import BeautifulSoup
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
import sys

# --------------------------------------------------
# CONFIGURATION AVANCÉE
# --------------------------------------------------

# Chargement des variables d'environnement
load_dotenv()

# Constantes
SAVENES_COORDS = (43.8345, 1.2059)
RAYON_KM = 15
NIVEAU_ETUDE = "bac"
LOCALISATION = "Savenès (82600)"
TIMEZONE = pytz.timezone('Europe/Paris')
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36"
CACHE_DURATION = timedelta(hours=1)  # Durée du cache des localisations

# Configuration des API
API_CONFIG = {
    'indeed': {
        'url': "https://api.indeed.com/ads/apisearch",
        'params': {
            "publisher": os.getenv('INDEED_API_KEY'),
            "q": NIVEAU_ETUDE,
            "l": LOCALISATION,
            "radius": RAYON_KM,
            "sort": "date",
            "jt": "fulltime,parttime",
            "explvl": "entry_level",
            "limit": 25,
            "fromage": 7,
            "v": "2",
            "format": "json"
        }
    },
    'hellowork': {
        'url': "https://api.hellowork.com/api/v1/jobs/search",
        'params': {
            "query": NIVEAU_ETUDE,
            "location": LOCALISATION,
            "radius": RAYON_KM,
            "educationLevel": "bac",
            "page": 1,
            "limit": 50
        }
    },
    'pole_emploi': {
        'url': "https://api.emploi-store.fr/partenaire/offresdemploi/v2/offres/search",
        'params': {
            "motsCles": NIVEAU_ETUDE,
            "commune": "82600",
            "rayon": RAYON_KM,
            "niveauQualification": "3",
            "range": "0-49"
        },
        'headers': {
            'Authorization': f'Bearer {os.getenv("POLE_EMPLOI_TOKEN")}'
        }
    }
}

# Configuration email
EMAIL_CONFIG = {
    'sender': os.getenv('EMAIL_SENDER'),
    'password': os.getenv('EMAIL_PASSWORD'),
    'receiver': os.getenv('EMAIL_RECEIVER'),
    'smtp_server': 'smtp.gmail.com',
    'smtp_port': 587
}

# Configuration base de données
DB_CONFIG = {
    'path': 'jobs_database.db',
    'tables': {
        'jobs': '''
            CREATE TABLE IF NOT EXISTS jobs (
                id TEXT PRIMARY KEY,
                platform TEXT,
                title TEXT,
                company TEXT,
                location TEXT,
                date TEXT,
                link TEXT,
                description TEXT,
                salary TEXT,
                contract_type TEXT,
                experience TEXT,
                skills TEXT,
                processed INTEGER DEFAULT 0,
                favorite INTEGER DEFAULT 0,
                created_at TEXT,
                updated_at TEXT
            )
        ''',
        'locations': '''
            CREATE TABLE IF NOT EXISTS locations (
                address TEXT PRIMARY KEY,
                latitude REAL,
                longitude REAL,
                last_updated TEXT
            )
        '''
    }
}

# Configuration logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        RotatingFileHandler('job_scraper.log', maxBytes=5*1024*1024, backupCount=3),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# --------------------------------------------------
# CLASSES PRINCIPALES
# --------------------------------------------------

class DatabaseManager:
    """Gère toutes les opérations de base de données"""
    def __init__(self):
        self.conn = sqlite3.connect(DB_CONFIG['path'])
        self.create_tables()
        
    def create_tables(self):
        """Crée les tables nécessaires si elles n'existent pas"""
        with self.conn:
            for table_sql in DB_CONFIG['tables'].values():
                self.conn.execute(table_sql)
    
    def save_job(self, job_data):
        """Sauvegarde ou met à jour une offre d'emploi"""
        existing = self.conn.execute(
            "SELECT id FROM jobs WHERE id = ?", (job_data['id'],)
        ).fetchone()
        
        now = datetime.now(TIMEZONE).isoformat()
        
        if existing:
            self.conn.execute(
                '''UPDATE jobs SET 
                    title = ?, company = ?, location = ?, date = ?, link = ?, 
                    description = ?, updated_at = ? 
                    WHERE id = ?''',
                (job_data['title'], job_data['company'], job_data['location'],
                 job_data['date'], job_data['link'], job_data['description'],
                 now, job_data['id'])
            )
        else:
            self.conn.execute(
                '''INSERT INTO jobs 
                    (id, platform, title, company, location, date, link, 
                    description, created_at, updated_at) 
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                (job_data['id'], job_data['platform'], job_data['title'],
                 job_data['company'], job_data['location'], job_data['date'],
                 job_data['link'], job_data['description'], now, now)
            )
    
    def get_seen_jobs(self):
        """Récupère les IDs des offres déjà vues"""
        return set(row[0] for row in self.conn.execute(
            "SELECT id FROM jobs"
        ).fetchall())
    
    def close(self):
        """Ferme la connexion à la base de données"""
        self.conn.close()

class GeoCache:
    """Cache pour les résultats de géocodage"""
    def __init__(self, db_manager):
        self.db_manager = db_manager
        self.cache = {}
        self.load_cache()
    
    def load_cache(self):
        """Charge le cache depuis la base de données"""
        for row in self.db_manager.conn.execute(
            "SELECT address, latitude, longitude FROM locations"
        ).fetchall():
            self.cache[row[0]] = (row[1], row[2])
    
    def get_coordinates(self, address):
        """Récupère les coordonnées depuis le cache ou l'API"""
        # Vérifier d'abord en mémoire
        if address in self.cache:
            return self.cache[address]
        
        # Vérifier en base de données
        row = self.db_manager.conn.execute(
            "SELECT latitude, longitude FROM locations WHERE address = ?",
            (address,)
        ).fetchone()
        
        if row:
            self.cache[address] = (row[0], row[1])
            return (row[0], row[1])
        
        # Si pas trouvé, utiliser l'API
        geolocator = Nominatim(user_agent="job_scraper")
        try:
            location = geolocator.geocode(f"{address}, France")
            if location:
                coords = (location.latitude, location.longitude)
                
                # Mettre à jour le cache et la base
                self.cache[address] = coords
                now = datetime.now(TIMEZONE).isoformat()
                
                self.db_manager.conn.execute(
                    '''INSERT OR REPLACE INTO locations 
                        (address, latitude, longitude, last_updated) 
                        VALUES (?, ?, ?, ?)''',
                    (address, coords[0], coords[1], now)
                )
                
                return coords
        except Exception as e:
            logger.error(f"Erreur de géocodage pour {address}: {e}")
        
        return None

class JobScraper:
    """Classe principale pour la recherche d'emploi"""
    def __init__(self):
        self.db = DatabaseManager()
        self.geo_cache = GeoCache(self.db)
        self.session = requests.Session()
        self.session.headers.update({'User-Agent': USER_AGENT})
        
        # Configuration du proxy si nécessaire
        if os.getenv('USE_PROXY', '').lower() == 'true':
            self.session.proxies = {
                'http': os.getenv('PROXY_URL'),
                'https': os.getenv('PROXY_URL')
            }
    
    def __del__(self):
        self.db.close()
    
    def check_distance(self, location):
        """Vérifie si une localisation est dans le rayon souhaité"""
        coords = self.geo_cache.get_coordinates(location)
        if coords:
            distance = geodesic(SAVENES_COORDS, coords).km
            return distance <= RAYON_KM
        return False
    
    def filter_by_education(self, description):
        """Filtre les offres pour ne garder que celles nécessitant uniquement le bac"""
        if not description:
            return False
            
        description = description.lower()
        
        # Termes positifs (doivent être présents)
        positive_terms = [
            r'\bbac\b', r'\bbaccalauréat\b', 'niveau bac',
            'diplôme secondaire', 'niveau iii'
        ]
        
        # Termes négatifs (ne doivent pas être présents)
        negative_terms = [
            r'bac\+2', r'bac \+2', r'bac.*2', r'bts\b', r'dut\b', 
            r'deug\b', r'bac\+3', r'bac \+3', r'bac.*3', r'licence\b',
            r'bachelor\b', r'bac\+4', r'bac \+4', r'bac.*4', r'bac\+5', 
            r'bac \+5', r'bac.*5', r'master\b', r'ingénieur\b',
            r'niveau iv', r'niveau ii', r'niveau i', r'école d\'ingénieur',
            r'grande école', r'maîtrise\b', r'doctorat\b', r'phd\b'
        ]
        
        # Vérification des termes positifs
        has_positive = any(re.search(term, description) for term in positive_terms)
        
        # Vérification des termes négatifs
        has_negative = any(re.search(term, description) for term in negative_terms)
        
        return has_positive and not has_negative
    
    def extract_salary(self, description):
        """Extrait le salaire de la description"""
        if not description:
            return None
            
        patterns = [
            r'(\d{1,3}(?:\s?\d{3})*\s?(?:€|euros?|EUR)',  # 30 000 €
            r'(?:salaire|rémunération).{1,20}?\b(\d{1,3}(?:\s?\d{3})*\b)',  # Salaire: 30000
            r'\b(\d{1,3}(?:\s?\d{3})*\s?(?:€|euros?|EUR).{1,20}?(?:annuel|an|mensuel|mois)\b'  # 2500 €/mois
        ]
        
        for pattern in patterns:
            match = re.search(pattern, description, re.IGNORECASE)
            if match:
                return match.group(1).replace(' ', '') + ' €'
        
        return None
    
    def extract_contract_type(self, description):
        """Extrait le type de contrat de la description"""
        if not description:
            return None
            
        contract_types = {
            'cdi': ['cdi', 'contrat à durée indéterminée'],
            'cdd': ['cdd', 'contrat à durée déterminée'],
            'interim': ['intérim', 'interim', 'mission intérim'],
            'alternance': ['alternance', 'apprentissage'],
            'stage': ['stage', 'stagiare']
        }
        
        description = description.lower()
        for contract, keywords in contract_types.items():
            if any(keyword in description for keyword in keywords):
                return contract
                
        return None
    
    def fetch_api_data(self, platform):
        """Récupère les données depuis une API de plateforme"""
        config = API_CONFIG.get(platform)
        if not config:
            return []
            
        try:
            response = self.session.get(
                config['url'],
                params=config.get('params', {}),
                headers=config.get('headers', {}),
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            logger.error(f"Erreur avec {platform} API: {e}")
            return None
    
    def process_hellowork_jobs(self, data):
        """Traite les données de HelloWork"""
        jobs = []
        for offer in data.get('results', []):
            job_id = offer.get('id')
            if not job_id:
                continue
                
            description = offer.get('description', '')
            if not self.filter_by_education(description):
                continue
                
            jobs.append({
                'id': f"hellowork_{job_id}",
                'platform': 'HelloWork',
                'title': offer.get('title', ''),
                'company': offer.get('company', {}).get('name', ''),
                'location': offer.get('location', {}).get('city', ''),
                'date': offer.get('publicationDate', ''),
                'link': offer.get('url', ''),
                'description': description,
                'salary': self.extract_salary(description),
                'contract_type': self.extract_contract_type(description)
            })
        
        return jobs
    
    def process_indeed_jobs(self, data):
        """Traite les données de Indeed"""
        jobs = []
        for result in data.get('results', []):
            job_id = result.get('jobkey')
            if not job_id:
                continue
                
            description = result.get('snippet', '') + ' ' + result.get('jobTitle', '')
            if not self.filter_by_education(description):
                continue
                
            jobs.append({
                'id': f"indeed_{job_id}",
                'platform': 'Indeed',
                'title': result.get('jobtitle', ''),
                'company': result.get('company', ''),
                'location': result.get('formattedLocation', ''),
                'date': result.get('date', ''),
                'link': result.get('url', ''),
                'description': description,
                'salary': result.get('salary', '') or self.extract_salary(description),
                'contract_type': self.extract_contract_type(description)
            })
        
        return jobs
    
    def process_pole_emploi_jobs(self, data):
        """Traite les données de Pôle Emploi"""
        jobs = []
        for offer in data.get('resultats', []):
            job_id = offer.get('id')
            if not job_id:
                continue
                
            description = offer.get('description', '')
            if not self.filter_by_education(description):
                continue
                
            jobs.append({
                'id': f"pole_emploi_{job_id}",
                'platform': 'France Travail',
                'title': offer.get('intitule', ''),
                'company': offer.get('entreprise', {}).get('nom', ''),
                'location': offer.get('lieuTravail', {}).get('libelle', ''),
                'date': offer.get('dateCreation', ''),
                'link': f"https://candidat.francetravail.fr/offres/recherche/detail/{job_id}",
                'description': description,
                'salary': offer.get('salaire', {}).get('libelle', '') or self.extract_salary(description),
                'contract_type': self.extract_contract_type(description)
            })
        
        return jobs
    
    def scrape_additional_sources(self):
        """Scrape des sources supplémentaires sans API"""
        jobs = []
        
        # Exemple avec un scraping de site (à adapter)
        try:
            url = "https://www.emploici.fr/offres-emploi?q=bac&l=Savenès%20(82600)&rayon=15"
            response = self.session.get(url, timeout=10)
            soup = BeautifulSoup(response.text, 'html.parser')
            
            for item in soup.select('.offer-card'):
                title = item.select_one('.offer-title').get_text(strip=True)
                company = item.select_one('.offer-company').get_text(strip=True)
                location = item.select_one('.offer-location').get_text(strip=True)
                link = item.select_one('a')['href']
                description = item.select_one('.offer-desc').get_text(strip=True)
                
                if self.filter_by_education(description):
                    jobs.append({
                        'id': f"emploici_{hash(link)}",
                        'platform': 'Emploici',
                        'title': title,
                        'company': company,
                        'location': location,
                        'date': datetime.now(TIMEZONE).strftime('%Y-%m-%d'),
                        'link': link,
                        'description': description,
                        'salary': self.extract_salary(description),
                        'contract_type': self.extract_contract_type(description)
                    })
        except Exception as e:
            logger.error(f"Erreur lors du scraping Emploici: {e}")
        
        return jobs
    
    def get_new_jobs(self):
        """Récupère toutes les nouvelles offres d'emploi"""
        seen_jobs = self.db.get_seen_jobs()
        all_jobs = []
        
        # Utilisation du multithreading pour les appels API
        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = {
                executor.submit(self.fetch_api_data, 'hellowork'): 'hellowork',
                executor.submit(self.fetch_api_data, 'indeed'): 'indeed',
                executor.submit(self.fetch_api_data, 'pole_emploi'): 'pole_emploi',
                executor.submit(self.scrape_additional_sources): 'scraping'
            }
            
            for future in as_completed(futures):
                platform = futures[future]
                try:
                    data = future.result()
                    if not data:
                        continue
                        
                    if platform == 'hellowork':
                        jobs = self.process_hellowork_jobs(data)
                    elif platform == 'indeed':
                        jobs = self.process_indeed_jobs(data)
                    elif platform == 'pole_emploi':
                        jobs = self.process_pole_emploi_jobs(data)
                    else:
                        jobs = data
                    
                    # Filtrer les jobs déjà vus et vérifier la localisation
                    for job in jobs:
                        if job['id'] not in seen_jobs and self.check_distance(job['location']):
                            all_jobs.append(job)
                            
                except Exception as e:
                    logger.error(f"Erreur lors du traitement {platform}: {e}")
        
        return all_jobs
    
    def save_jobs_to_db(self, jobs):
        """Sauvegarde les jobs dans la base de données"""
        for job in jobs:
            self.db.save_job(job)
    
    def generate_email_content(self, jobs):
        """Génère le contenu HTML pour l'email"""
        if not jobs:
            return None
            
        # Style CSS pour l'email
        style = """
            <style>
                body { font-family: Arial, sans-serif; line-height: 1.6; }
                .job { border: 1px solid #ddd; padding: 15px; margin-bottom: 15px; border-radius: 5px; }
                .job-title { color: #2c3e50; font-size: 18px; margin-top: 0; }
                .job-meta { color: #7f8c8d; font-size: 14px; }
                .job-description { margin: 10px 0; }
                .job-link { display: inline-block; background: #3498db; color: white; padding: 5px 10px; text-decoration: none; border-radius: 3px; }
                .platform-tag { display: inline-block; background: #e74c3c; color: white; padding: 2px 5px; font-size: 12px; border-radius: 3px; margin-left: 5px; }
            </style>
        """
        
        # Construction du HTML
        html_content = f"""
        <html>
            <head>{style}</head>
            <body>
                <h2>{len(jobs)} nouvelles offres d'emploi trouvées</h2>
                <p>Voici les nouvelles offres nécessitant uniquement le bac dans un rayon de {RAYON_KM} km autour de {LOCALISATION}:</p>
        """
        
        for job in jobs:
            html_content += f"""
                <div class="job">
                    <h3 class="job-title">{job['title']} <span class="platform-tag">{job['platform']}</span></h3>
                    <div class="job-meta">
                        <strong>{job['company']}</strong> - {job['location']} - {job['date']}
                    </div>
                    {job.get('salary', '') and f'<div class="job-meta"><strong>Salaire:</strong> {job["salary"]}</div>'}
                    {job.get('contract_type', '') and f'<div class="job-meta"><strong>Type de contrat:</strong> {job["contract_type"].upper()}</div>'}
                    <div class="job-description">
                        {job['description'][:200]}...
                    </div>
                    <a href="{job['link']}" class="job-link">Voir l'offre</a>
                </div>
            """
        
        html_content += """
                <p><em>Cette recherche est effectuée automatiquement. Vous pouvez ajuster les paramètres dans le script.</em></p>
            </body>
        </html>
        """
        
        return html_content
    
    def send_email_notification(self, jobs):
        """Envoie une notification par email avec les nouvelles offres"""
        if not jobs or not EMAIL_CONFIG.get('sender'):
            return
            
        html_content = self.generate_email_content(jobs)
        if not html_content:
            return
            
        subject = f"🚀 {len(jobs)} nouvelles offres d'emploi bac autour de {LOCALISATION}"
        
        msg = MIMEMultipart('alternative')
        msg['Subject'] = subject
        msg['From'] = EMAIL_CONFIG['sender']
        msg['To'] = EMAIL_CONFIG['receiver']
        
        part = MIMEText(html_content, 'html')
        msg.attach(part)
        
        try:
            with smtplib.SMTP(EMAIL_CONFIG['smtp_server'], EMAIL_CONFIG['smtp_port']) as server:
                server.starttls()
                server.login(EMAIL_CONFIG['sender'], EMAIL_CONFIG['password'])
                server.send_message(msg)
            logger.info("Notification email envoyée avec succès")
        except Exception as e:
            logger.error(f"Erreur lors de l'envoi de l'email: {e}")
    
    def run_search(self):
        """Exécute une recherche complète"""
        logger.info("Lancement de la recherche d'emploi...")
        start_time = time.time()
        
        try:
            new_jobs = self.get_new_jobs()
            if new_jobs:
                self.save_jobs_to_db(new_jobs)
                self.send_email_notification(new_jobs)
                
                # Sauvegarde des résultats dans un fichier JSON
                timestamp = datetime.now(TIMEZONE).strftime("%Y%m%d_%H%M%S")
                filename = f"results/offres_{timestamp}.json"
                os.makedirs('results', exist_ok=True)
                
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(new_jobs, f, ensure_ascii=False, indent=2)
                
                logger.info(f"{len(new_jobs)} nouvelles offres trouvées et sauvegardées dans {filename}")
            else:
                logger.info("Aucune nouvelle offre trouvée")
                
        except Exception as e:
            logger.error(f"Erreur critique lors de la recherche: {e}")
        finally:
            elapsed_time = time.time() - start_time
            logger.info(f"Recherche terminée en {elapsed_time:.2f} secondes")

# --------------------------------------------------
# FONCTIONS UTILITAIRES ET EXECUTION
# --------------------------------------------------

def run_scheduled_search():
    """Exécute la recherche selon un planning"""
    scraper = JobScraper()
    
    # Planification des recherches
    schedule.every().hour.at(":30").do(scraper.run_search)  # Toutes les heures à :30
    schedule.every().day.at("08:00").do(scraper.run_search)  # Tous les jours à 8h
    
    logger.info("Démarrage du service de recherche planifiée...")
    
    while True:
        schedule.run_pending()
        time.sleep(60)

def run_once():
    """Exécute une seule recherche"""
    scraper = JobScraper()
    scraper.run_search()

if __name__ == "__main__":
    # Vérifier les arguments pour le mode d'exécution
    if len(sys.argv) > 1 and sys.argv[1] == '--daemon':
        # Mode service (planifié)
        run_scheduled_search()
    else:
        # Mode one-shot
        run_once()