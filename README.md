# 二叉堆程序验证

本次作业在树上基本完成了二叉堆与数组算法描述对应的验证、与树算法描述对应的验证（存在 admit，见下文 tree_pop.v）和算法功能的验证。主要结构如下。

## 文件结构

### heap.c

本次验证的 C 程序代码。

### definitions.v

关于 VST 的基本命题，包括 all_int 和数组内 swap 的分离逻辑命题。

### list_relation.v

定义程序与 list 实现的关系。

### tree_list.v

树的各种定义；定义 list 与 tree 的对应关系和基本引理。

### tree_up.v

定义树上的 up 关系以及和 list 关系的统一性。

### tree_down.v

定义树上的 down 关系以及和 list 关系的统一性。

### tree_push.v

定义树上的 push 关系以及和 list 关系的统一性。

在 push 的时候，通过定义出完全二叉树的 next_index 将树抛成 partial_tree，从而接上要加入的值。

### tree_pop.v

定义树上的 pop 关系以及和 list 关系的统一性。

类似地，我们定义出了完全二叉树的最后一个节点编号 last_index 将树抛开，从而删去树的最后一个节点并把其值放到树根。

在本文件中，我们 admit 了两个对称的引理，这两个引理较为细节，含义是如果一棵树 (Node v ls rs) 对应到了一个 list l、最后一个节点不在 ls/rs 子树中，那么 ls/rs 可以对应到 l 删除末尾元素所得到的 list l' 上。

### tree_set.v

在树上定义 set 与树的对应关系以及验证算法功能的正确性。