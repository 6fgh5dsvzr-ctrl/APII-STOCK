import { createClient } from '@supabase/supabase-js';

const url = import.meta.env.VITE_SUPABASE_URL;
const anonKey = import.meta.env.VITE_SUPABASE_ANON_KEY;

// eslint-disable-next-line no-console
console.info('[stock-apii] build-marker-2 — Supabase URL configurée : ' + Boolean(url) + ', clé configurée : ' + Boolean(anonKey));

if (!url || !anonKey) {
  // eslint-disable-next-line no-console
  console.warn('Supabase non configuré : définissez VITE_SUPABASE_URL et VITE_SUPABASE_ANON_KEY (.env).');
}

export const supabase = url && anonKey ? createClient(url, anonKey) : null;
