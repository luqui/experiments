#include <memory>
#include <vector>
#include <iostream>


template<class T> class TxPtr;

class Reader
{
public:
    struct LogEntBase
    {
        virtual ~LogEntBase() = default;
    };

    template<class T>
    struct LogEnt : public LogEntBase
    {
        LogEnt(const TxPtr<T>* ptr) : ptr(ptr) { }

        const TxPtr<T>* ptr;
    };

    template<class T>
    void addLog(const TxPtr<T>* ptr)
    {
        m_readLog.push_back(std::unique_ptr<LogEntBase>(new LogEnt<T> { ptr }));
    }
private:
    std::vector<std::unique_ptr<LogEntBase>> m_readLog;
};

class Writer
{
public:
    struct LogEntBase
    {
        virtual ~LogEntBase() = default;
        virtual void commit() = 0;
        virtual void* lookup(void*) const = 0;
    };
    
    template<class T>
    struct LogEnt : public LogEntBase
    {
        LogEnt(TxPtr<T>* ptr, std::unique_ptr<T> value) : ptr(ptr), value(std::move(value)) { }

        void commit() override;
        void* lookup(void* needle) const override;

        TxPtr<T>* ptr;
        std::unique_ptr<T> value;
    };


    ~Writer()
    {
        if (!m_writeLog.empty())
        {
            std::abort();
        }
    }

    template <class T>
    T* addLog(TxPtr<T>* ptr, std::unique_ptr<T> clone);

    template<class T>
    T* lookup(TxPtr<T>* ptr)
    {
        for (auto& i : m_writeLog)
        {
            if (void* r = i->lookup(ptr))
            {
                return static_cast<T*>(r);
            }
        }
        return nullptr;
    }

    void commit()
    {
        // TODO lock
        for (auto& i : m_writeLog)
        {
            i->commit();
        }
        m_writeLog.clear();
    }

    void abort()
    {
        m_writeLog.clear();
    }
private:
    std::vector<std::unique_ptr<LogEntBase>> m_writeLog;
};

template<class T>
class TxPtr
{
    friend class Writer;
public:
    TxPtr(std::unique_ptr<T> p) : m_value(p.release())
    { }

    // Copying is allowed, and it does a shallow pointer copy (with GC).
    TxPtr(const TxPtr&) = default;

    const T* read(Reader& reader) const
    {
        reader.addLog<T>(this);
        return m_value.get();
    }

    const T* read(Writer& writer) const
    {
        // TODO: I think Writer should have a "read-only" log, so we don't have to unnecessarily clone.
        return const_cast<const T*>(const_cast<TxPtr*>(this)->write(writer));
    }

    T* write(Writer& writer)
    {
        // XXX what if T is abstract?  should use m_value->shallowClone()
        if (T* value = writer.lookup(this))
        {
            return value;
        }
        else {
            return writer.addLog<T>(this, std::make_unique<T>(*m_value));
        }
    }

private:
    std::shared_ptr<T> m_value;
};


template<class T>
T* Writer::addLog(TxPtr<T> *ptr, std::unique_ptr<T> clone)
{
    // We expect the returned T* to be immediately dereferenced in terms of ->.
    T* ret = clone.get();
    m_writeLog.push_back(std::unique_ptr<LogEntBase>(new Writer::LogEnt<T>(ptr, std::move(clone))));
    return ret;
}

template<class T>
void* Writer::LogEnt<T>::lookup(void* needle) const
{
    if (needle == ptr)
    {
        return value.get();
    }
    else
    {
        return nullptr;
    }
}

template<class T>
void Writer::LogEnt<T>::commit()
{
    ptr->m_value.reset(value.release());
}



struct ModelThingA
{
    int x = 0;
};

struct ModelThingB
{
    int y = 0;
    TxPtr<ModelThingA> thingA = std::make_unique<ModelThingA>();
};

struct Model
{
    TxPtr<ModelThingB> thingB = std::make_unique<ModelThingB>();
};

TxPtr<Model> MODEL = std::make_unique<Model>();

void readTest()
{
    Reader r;
    // int x = r.read(r.read(r.read(MODEL)->thingB)->thingA)->x;
    std::cout << "READ " << MODEL.read(r)->thingB.read(r)->thingA.read(r)->x << "\n";
}

int main()
{
    readTest();

    Writer w;
    MODEL.write(w)->thingB.write(w)->thingA.write(w)->x = 1;
    readTest();
    std::cout << "WRITE " << MODEL.read(w)->thingB.read(w)->thingA.read(w)->x << "\n";
    w.commit();
    readTest();
}
