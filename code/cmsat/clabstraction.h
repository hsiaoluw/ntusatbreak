#ifndef __CL_ABSTRACTION__H__
#define __CL_ABSTRACTION__H__

#define CL_ABST_TYPE uint32_t
#define CLAUSE_ABST_SIZE 32

inline CL_ABST_TYPE abst_var(const uint32_t v)
{
    return 1UL << (v % CLAUSE_ABST_SIZE);
}

template <class T> CL_ABST_TYPE calcAbstraction(const T& ps)
{
    CL_ABST_TYPE abstraction = 0;

    for (uint16_t i = 0; i != ps.size(); i++)
        abstraction |= abst_var(ps[i].var());

    return abstraction;
}

#endif //__CL_ABSTRACTION__H__
