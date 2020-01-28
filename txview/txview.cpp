#include <memory>
#include <vector>
#include <iostream>
#include <set>


template<class T> class TxPtr;
class Reader;

class RefreshListener
{
public:
    virtual ~RefreshListener() = default;
    virtual void refresh(Reader&) = 0;
};

class Reader
{
public:
    Reader(RefreshListener* watch) : m_watch(watch)
    { }

    template<class T>
    void logRead(const TxPtr<T>* ptr)
    {
        // XXX yuck const_cast
        const_cast<TxPtr<T>*>(ptr)->addWatch(m_watch);
    }
private:
    RefreshListener* m_watch;
};

class Writer
{
public:
    struct LogEntBase
    {
        virtual ~LogEntBase() = default;
        virtual void commit() = 0;
        virtual void* lookup(void*) const = 0;
        virtual void notify() = 0;
    };
    
    template<class T>
    struct LogEnt : public LogEntBase
    {
        LogEnt(TxPtr<T>* ptr, std::unique_ptr<T> value) : ptr(ptr), value(std::move(value)) { }

        void commit() override;
        void* lookup(void* needle) const override;
        void notify() override;

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
        std::vector<RefreshListener*> listeners;
        for (auto& i : m_writeLog)
        {
            i->commit();
        }
        // Should we clear the log here?
        for (auto& i  : m_writeLog)
        {
            i->notify();
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
    TxPtr()
    { }

    TxPtr(std::unique_ptr<T> p) : m_value(p.release())
    { }

    // Copying is allowed, and it does a shallow pointer copy (with GC).
    TxPtr(const TxPtr&) = default;

    const T* read(Reader& reader) const
    {
        reader.logRead<T>(this);
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
        else if (!m_value)
        {
            return nullptr; // XXX logRead?
        }
        else
        {
            return writer.addLog<T>(this, std::make_unique<T>(*m_value));
        }
    }

    void addWatch(RefreshListener* listener)
    {
        m_watches.insert(listener);
    }

    void notify()
    {
        std::set<RefreshListener*> watches = m_watches;
        m_watches.clear();  // XXX correct?
        for (auto w : watches)
        {
            Reader reader(w);
            w->refresh(reader);
        }
    }

private:
    std::shared_ptr<T> m_value;
    std::set<RefreshListener*> m_watches;
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

template<class T>
void Writer::LogEnt<T>::notify()
{
    ptr->notify();
}


struct Tree
{
    Tree(int data) : data(data)
    { }

    int data;
    TxPtr<Tree> left;
    TxPtr<Tree> right;
};

struct NodeView : public RefreshListener
{
    NodeView(TxPtr<Tree> ptr)
    : model(ptr)
    {
        static int ctr = 0;
        id = ctr++;
    }

    void refresh(Reader& reader) override
    {
        std::cout << "REFRESH NodeView " << id << "\n";
        // TODO detect if each child changed?
        left.reset(new NodeView(model.read(reader)->left));
        right.reset(new NodeView(model.read(reader)->right));
    }

    void show(int indent)
    {
        Reader tx(this);
        for (int i = 0; i < indent; i++)
        {
            std::cout << "  ";
        }
        const Tree* modelp = model.read(tx);
        std::cout << modelp->data << "\n";
    }

    int id;
    TxPtr<Tree> model;
    std::unique_ptr<NodeView> left;
    std::unique_ptr<NodeView> right;
};

void insert(Writer& tx, TxPtr<Tree>& root, int value)
{
    Tree* modelp = root.write(tx);
    if (!modelp)
    {
        root = TxPtr<Tree>(std::make_unique<Tree>(value));
    }
    else if (value <= modelp->data)
    {
        insert(tx, modelp->left, value);
    }
    else
    {
        insert(tx, modelp->right, value);
    }
}

int main()
{
    TxPtr<Tree> model (std::make_unique<Tree>(0));
    NodeView view (model);

    while (true)
    {
        view.show(0);

        std::cout << "Insert? ";
        int x;
        std::cin >> x;

        {
            Writer tx;
            insert(tx, model, x);
            tx.commit();
        }
    }
}