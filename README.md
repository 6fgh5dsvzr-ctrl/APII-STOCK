# Stock APII

Application de gestion de stock (matériel, consommables, commandes, masques) pour APII.
Portage de l'artifact Claude vers un vrai projet React (Vite) + Supabase, déployable sur Vercel.

## Statut

- ✅ Projet Supabase **STOCK-APII** créé (org APII-MTP, région `eu-central-1`), table `kv_store` en place avec RLS.
- ✅ `.env` déjà rempli avec l'URL et la clé publique de ce projet — rien à configurer pour tester en local.
- ⬜ Pas encore déployé sur Vercel.
- ⬜ Pas encore testé en local (Node.js n'est pas installé sur la machine où tourne Claude — à faire de votre côté).

## 1. Prérequis

- [Node.js](https://nodejs.org/) 18+ installé sur votre machine (`node -v` pour vérifier).
- Un compte [Vercel](https://vercel.com) (gratuit), pour le déploiement.

## 2. Installer et tester en local

```bash
cd "stock-apii"
npm install
npm run dev
```

Ouvrez l'URL affichée (ex. `http://localhost:5173`). Le `.env` pointe déjà vers le projet Supabase `STOCK-APII` :
créez un profil test, il doit apparaître dans la table `kv_store` sur [supabase.com](https://supabase.com/dashboard/project/gjdjcohwbkisyyllyokf/editor).

## 3. Déployer sur Vercel

**Option A — via l'interface web (le plus simple) :**

1. Poussez ce dossier sur un dépôt GitHub.
2. Sur [vercel.com/new](https://vercel.com/new), importez le dépôt.
3. Dans les paramètres du projet Vercel, ajoutez les variables d'environnement `VITE_SUPABASE_URL` et
   `VITE_SUPABASE_ANON_KEY` avec les valeurs de votre `.env` local (le fichier `.env` n'est pas poussé sur GitHub,
   c'est normal — il est dans `.gitignore`).
4. Déployez. Vite/React est détecté automatiquement (build : `npm run build`, sortie : `dist`).

**Option B — via la CLI :**

```bash
npm install -g vercel
vercel login
vercel          # premier déploiement (suivez les questions)
vercel env add VITE_SUPABASE_URL
vercel env add VITE_SUPABASE_ANON_KEY
vercel --prod
```

## Sécurité — à lire avant de mettre en production

La table `kv_store` est protégée par une politique Supabase **permissive** (`supabase/schema.sql`) : toute personne
qui connaît l'URL du site et la clé publique (visible dans le code JS envoyé au navigateur — c'est normal pour
Supabase) peut lire et écrire les données. L'application elle-même n'a qu'un code PIN interne, pas une vraie
authentification.

C'est le même niveau de protection que l'artifact Claude d'origine pour les données elles-mêmes, mais **sans** la
restriction "réservé aux membres de votre organisation" qu'offrait l'artifact. Pour resserrer l'accès, plusieurs
options (à faire au besoin, pas incluses ici) :

- **Protection Vercel** (Password Protection / Vercel Authentication, plans payants) pour limiter qui peut même
  charger le site.
- **Restreindre par IP/VPN** si l'app n'est utilisée qu'en interne.
- **API route côté serveur** : au lieu d'écrire directement depuis le navigateur vers Supabase, passer par une
  fonction Vercel qui vérifie un secret avant d'écrire — plus de travail, mais plus robuste.

## Structure du projet

```
src/
  App.jsx            composant principal (porté tel quel depuis l'artifact)
  main.jsx           point d'entrée React
  lib/
    supabaseClient.js  client Supabase (lit VITE_SUPABASE_URL / VITE_SUPABASE_ANON_KEY)
    storage.js         remplace window.storage.get/set/delete de l'artifact d'origine
supabase/
  schema.sql          schéma SQL déjà appliqué au projet Supabase STOCK-APII
```
