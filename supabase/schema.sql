-- Table de stockage clé/valeur partagée pour Stock APII.
-- Une seule ligne (key = 'apii-stock-v3') contient tout l'état de
-- l'application (utilisateurs, matériel, consommables, commandes,
-- journal...) sous forme de JSON — même logique que l'artifact d'origine,
-- mais sans la limite de 256 Ko par document.

create table if not exists kv_store (
  key text primary key,
  value text not null,
  updated_at timestamptz not null default now()
);

alter table kv_store enable row level security;

-- Politique permissive : la clé "anon" (publique côté navigateur) peut tout
-- lire/écrire. Comme l'appli n'a pas de vraie authentification par compte
-- (juste un code PIN interne), ce n'est pas plus permissif que l'artifact
-- Claude d'origine — mais contrairement à celui-ci, RIEN ne limite l'accès
-- aux seuls membres de votre organisation. Voir le README pour resserrer
-- l'accès (ex. protection Vercel, ou vérification d'un secret côté serveur).
create policy "kv_store_anon_all"
  on kv_store
  for all
  to anon
  using (true)
  with check (true);
