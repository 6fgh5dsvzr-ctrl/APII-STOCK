import { supabase } from './supabaseClient';

/*
 * Remplace l'API window.storage.get/set/delete(clé, partagé) utilisée par
 * App.jsx (héritée de l'environnement d'artifact Claude d'origine) :
 *   - partagé = true  -> table Supabase `kv_store` (partagée entre tous les
 *                        navigateurs qui ouvrent l'appli)
 *   - partagé = false -> localStorage (propre à ce navigateur, ex. la
 *                        session de connexion)
 */

const TABLE = 'kv_store';

async function get(key, partage) {
  if (!partage) {
    const v = localStorage.getItem(key);
    return v == null ? null : { value: v };
  }
  if (!supabase) return null;
  const { data, error } = await supabase.from(TABLE).select('value').eq('key', key).maybeSingle();
  if (error || !data) return null;
  return { value: data.value };
}

async function set(key, value, partage) {
  if (!partage) {
    localStorage.setItem(key, value);
    return true;
  }
  if (!supabase) return false;
  const { error } = await supabase.from(TABLE).upsert({ key, value, updated_at: new Date().toISOString() });
  return !error;
}

async function del(key, partage) {
  if (!partage) {
    localStorage.removeItem(key);
    return true;
  }
  if (!supabase) return false;
  const { error } = await supabase.from(TABLE).delete().eq('key', key);
  return !error;
}

window.storage = { get, set, delete: del };
