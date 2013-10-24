#include <storage/bdb_block_store.h>
#if 0
DBBlockStore::DBBlockStore() {
  opened = false;
  std::ostringstream oss;
  oss << "temp_block_store_" << PAPI_get_real_nsec();
  Open(oss.str());
}

DBBlockStore::DBBlockStore(std::string db_file_name) {
  opened = false;
  Open(db_file_name);
}

DBBlockStore::~DBBlockStore() {
  Close();
}

void DBBlockStore::Open(std::string db_file_name) {
  Close();
  env = new DbEnv(0);
  env->set_error_stream(&std::cout);
  env->set_cachesize(2, 0, 1);
  recursive_mkdir(db_file_name.c_str());
  env->open(db_file_name.c_str(), DB_CREATE | DB_INIT_MPOOL, 0);
  db = new Db(env, 0);
  if (db->open(NULL, "db", NULL, DB_HASH, DB_CREATE, 0)) {
    std::cerr << db_file_name << " block store open error. " << std::endl;
    exit(1);
  }
  opened = true;
}

void DBBlockStore::Close() {
  if (opened) {
    db->close(0);
    delete db;
    delete env;
    opened = false;
  }
}

static std::string keyToStr(const HashBlockStore::Key& k) {
  std::string ks;
  boost::to_string(k, ks);
  return ks;
}

bool DBBlockStore::get(const Key& key, Value& value) {
  return getVal(keyToStr(key), value);
}

void DBBlockStore::put(const Key& key, const Value& value) {
  putVal(keyToStr(key), value);
}

static std::string addrToStr(uint32_t addr) {
  std::ostringstream oss;
  oss << "RAM_" << addr;
  return oss.str();
}

bool DBBlockStore::getAddr(uint32_t addr, Value& value) {
  return getVal(addrToStr(addr), value);
}

void DBBlockStore::putAddr(uint32_t addr, const Value& value) {
  putVal(addrToStr(addr), value);
}

bool DBBlockStore::getVal(std::string key, Value& value) {
  if (!opened) {
    std::cout << "WARNING: trying to use an unopened block stored." << std::endl;
    return false;
  }
  Dbt k(const_cast<char*>(key.data()), key.size());
  Dbt v;
  if (db->get(NULL, &k, &v, 0) == DB_NOTFOUND) {
    return false;
  }
  value = Bits(string((char*)v.get_data()));
  return true;
}

void DBBlockStore::putVal(std::string key, const Value& value) {
  if (!opened) {
    std::cout << "WARNING: trying to use an unopened block stored." << std::endl;
    return;
  }
  std::string vs;
  boost::to_string(value, vs);

  Dbt k(const_cast<char*>(key.data()), key.size());
  Dbt v(const_cast<char*>(vs.data()), vs.size()+1);
  db->put(NULL, &k, &v, 0);
}

void DBBlockStore::free(const Key& key) {
  if (!opened) {
    std::cout << "WARNING: trying to use an unopened block stored." << std::endl;
    return;
  }
}
#endif
