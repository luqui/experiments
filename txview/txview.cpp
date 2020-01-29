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
    Reader(std::shared_ptr<RefreshListener> watch) : m_watch(watch)
    { }

    template<class T>
    void logRead(const TxPtr<T>* ptr)
    {
        // XXX yuck const_cast
        const_cast<TxPtr<T>*>(ptr)->addWatch(m_watch);
    }
private:
    std::shared_ptr<RefreshListener> m_watch;
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
        for (auto& i  : m_writeLog)
        {
            i->notify();
            m_writeLog.clear();
            break;
        }
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

    void addWatch(std::shared_ptr<RefreshListener> listener)
    {
        m_ctrl->watches.insert(listener);
    }

    void notify()
    {
        auto watches = m_ctrl->watches;
        m_ctrl->watches.clear();  // XXX correct?
        for (auto w : watches)
        {
            w->refresh();  // The crash here is due to a deleted listener being called.
                           // We need smarter automatic
        }
    }

    operator bool() { return static_cast<bool>(m_ctrl->value); }

//private:
    struct ControlBlock
    {
        std::unique_ptr<T> value;
        std::set<std::shared_ptr<RefreshListener>> watches;
    };

    std::shared_ptr<ControlBlock> m_ctrl;
};

template<class T>
class ModelTracker
{
public:
    ModelTracker(const TxPtr<T>& ptr) : ptr(ptr), m_listener(new Listener(this))
    { }

    ~ModelTracker()
    {
        m_listener->m_backptr = nullptr;
    }

    void listen(const std::function<void(Reader&)>& cb)
    {
        m_cb = cb;
        refresh();
    }

    TxPtr<T> ptr;
private:
    void refresh()
    {
        Reader reader(m_listener);
        if (m_cb)
        {
            m_cb(reader);
        }
    }

    struct Listener : public RefreshListener
    {
        Listener(ModelTracker* backptr) : m_backptr(backptr)
        { }

        void refresh() override
        {
            if (m_backptr)
            {
                m_backptr->refresh();
            }
        }
        ModelTracker* m_backptr;
    };

    std::function<void(Reader&)> m_cb;
    std::shared_ptr<Listener> m_listener;
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
    ptr->m_ctrl->value.swap(value);
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
    NodeView(const TxPtr<Tree>& ptr) : m_model(ptr)
    {
        static int ctr = 0;
        m_id = ctr++;
        std::cout << "CREATE NodeView " << m_id << "\n";

        m_model.listen([&](Reader& tx)
        {
            this->refresh(tx);
        });
    }

    void refresh(Reader& reader)
    {
        const Tree* node = m_model.ptr.read(reader);
        std::cout << "REFRESH NodeView " << m_id << " = " << node->data << "\n";
        // TODO detect if each child changed?
        if (auto left = node->left)
        {
            m_left.reset(new NodeView(left));
        }
        else{
            m_left.reset(nullptr);
        }

        if (auto right = node->right)
        {
            m_right.reset(new NodeView(right));
        }
        else
        {
            m_right.reset(nullptr);
        }
    }

    void show(int indent)
    {
        for (int i = 0; i < indent; i++)
        {
            std::cout << "  ";
        }
        std::cout << m_model.ptr.m_ctrl->value->data << "\n";
        if (m_left)
        {
            m_left->show(indent+1);
        }
        if (m_right)
        {
            m_right->show(indent+1);
        }
    }

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

void check(const TxPtr<Tree>& p)
{
    if (p.m_ctrl->value)
    {
        check(p.m_ctrl->value->left);
        check(p.m_ctrl->value->right);
    }
}

int main()
{
    TxPtr<Tree> model (std::make_unique<Tree>(0));
    NodeView view (model);

    while (true)
    {
        check(model);
        view.show(0);

        std::cout << "Insert? ";
        int x;
        std::cin >> x;

        {
            Writer tx;
            insert(tx, model, x);
            check(model);
            tx.commit();
            check(model);
        }
    }
}