#include <memory>
#include <vector>
#include <iostream>
#include <set>
#include <functional>


template<class T> class TxPtr;
class Reader;

class RefreshListener
{
public:
    virtual ~RefreshListener() = default;
    virtual void refresh() = 0;
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
    TxPtr() : m_ctrl(new ControlBlock)
    { }

    TxPtr(std::unique_ptr<T> p) : m_ctrl(new ControlBlock { std::move(p), {} })
    { }

    // Copying is allowed, and it does a shallow pointer copy (with GC).
    TxPtr(const TxPtr&) = default;

    const T* read(Reader& reader) const
    {
        reader.logRead<T>(this);
        return m_ctrl->value.get();
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
        else if (!m_ctrl->value)
        {
            return nullptr; // XXX logRead?
        }
        else
        {
            return writer.addLog<T>(this, std::make_unique<T>(*m_ctrl->value));
        }
    }

    void addWatch(RefreshListener* listener)
    {
        m_ctrl->watches.insert(listener);
    }

    void notify()
    {
        std::set<RefreshListener*> watches = m_ctrl->watches;
        m_ctrl->watches.clear();  // XXX correct?
        for (auto w : watches)
        {
            w->refresh();
        }
    }

    operator bool() { return static_cast<bool>(m_ctrl->value); }

private:
    struct ControlBlock
    {
        std::unique_ptr<T> value;
        std::set<RefreshListener*> watches;
    };

    std::shared_ptr<ControlBlock> m_ctrl;
};

template<class T>
class ModelTracker : public RefreshListener
{
public:
    ModelTracker(const TxPtr<T>& ptr) : ptr(ptr)
    { }

    void listen(const std::function<void(Reader&)>& cb)
    {
        m_cb = cb;
        Reader reader(this);
        m_cb(reader);
    }

    void refresh() override
    {
        Reader reader(this);
        if (m_cb)
        {
            m_cb(reader);
        }
    }

    const TxPtr<T>& ptr;
private:
    std::function<void(Reader&)> m_cb;
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
    ptr->m_ctrl->value.reset(value.release());
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

struct NodeView
{
    NodeView(TxPtr<Tree> ptr) : m_model(ptr)
    {
        static int ctr = 0;
        m_id = ctr++;

        m_model.listen([&](Reader& tx)
        {
            this->refresh(tx);
        });
    }

    void refresh(Reader& reader)
    {
        std::cout << "REFRESH NodeView " << m_id << "\n";
        // TODO detect if each child changed?
        if (auto left = m_model.ptr.read(reader)->left)
        {
            m_left.reset(new NodeView(left));
        }
        else{
            m_left.reset(nullptr);
        }

        if (auto right = m_model.ptr.read(reader)->right)
        {
            m_right.reset(new NodeView(m_model.ptr.read(reader)->right));
        }
        else
        {
            m_right.reset(nullptr);
        }
    }

    /*
    void show(int indent, Reader& reader)
    {
        Reader tx(this);
        for (int i = 0; i < indent; i++)
        {
            std::cout << "  ";
        }
        const Tree* modelp = m_model.read(tx);
        std::cout << modelp->data << "\n";
    }
     */

    int m_id;

    ModelTracker<Tree> m_model;
    std::unique_ptr<NodeView> m_left;
    std::unique_ptr<NodeView> m_right;
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
        //view.show(0);

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