import { createClient } from '@supabase/supabase-js';

const url = import.meta.env.VITE_SUPABASE_URL;
const anonKey = import.meta.env.VITE_SUPABASE_ANON_KEY;

if (!url || !anonKey) {
  // eslint-disable-next-line no-console
  console.warn('Supabase non configuré : définissez VITE_SUPABASE_URL et VITE_SUPABASE_ANON_KEY (.env).');
}

export const supabase = url && anonKey ? createClient(url, anonKey) : null;
