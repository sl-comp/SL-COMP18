/**
 * \file global_typdef.h
 * \brief Global typedef declarations.
 */

#ifndef SLCOMP_PARSER_GLOBAL_TYPEDEF_H
#define SLCOMP_PARSER_GLOBAL_TYPEDEF_H

#include <memory>
#include <vector>
#include <unordered_map>

template <class T> using sptr_t = std::shared_ptr<T>;
template <class T> using sptr_v = std::vector<std::shared_ptr<T>>;

template <class T1, class T2> using sptr_um1 = std::unordered_map<std::shared_ptr<T1>, std::shared_ptr<T2>>;
template <class T1, class T2> using sptr_um2 = std::unordered_map<T1, std::shared_ptr<T2>>;
template <class T1, class T2> using sptr_um3 = std::unordered_map<std::shared_ptr<T1>, T2>;

template <class T1, class T2> using umap = std::unordered_map<T1, T2>;

#endif //SLCOMP_PARSER_GLOBAL_TYPEDEF_H
