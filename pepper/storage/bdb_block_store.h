#ifndef DB_BLOCK_STORE_H_
#define DB_BLOCK_STORE_H_
#include <sstream>
#include <common/measurement.h>
#include <common/utility.h>

#if 0
#include <string>
#include <db_cxx.h>

#include <storage/hash_block_store.h>


class DBBlockStore : public HashBlockStore {
  public:
    DBBlockStore();
    DBBlockStore(std::string db_file_name);
    virtual ~DBBlockStore();
    virtual void Open(std::string db_file_name);
    virtual void Close();

    virtual bool get(const Key& key, Value& value);
    virtual void put(const Key& key, const Value& value);

    virtual bool getAddr(uint32_t addr, Value& value);
    virtual void putAddr(uint32_t addr, const Value& value);

    virtual void free(const Key& key);

  private:
    DbEnv* env;
    Db* db;

    bool getVal(std::string key, Value& value);
    void putVal(std::string key, const Value& value);
};
#endif
#endif /* DB_BLOCK_STORE_H_ */


