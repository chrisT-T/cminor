# 大作业报告

郑琬仪 2020012364 软02 



## 实现过程：

1. 检查是否所有Ranking function的非负性是否被相应的条件列表蕴含

2. 利用DFS找出路径 `list<List<Block>> res`
   - `foreach(List<Block> lisblk in res)` 就是以`Block`为单元的基本路径
   - `lisblk[0]` 表示前置条件块
   - `lisblk[lisblk.Count-1]` 表示后置条件块

3. 对于每一条路径
   1. 把所有分开的前置条件用 `AndExpression` 集合成前置条件

   2. 把所有分开的后置条件用 `AndExpression` 集合成前置条件

   3. 对于首尾的 `Block` 都是 `Head Block` 并且拥有相同秩函数数量的路径，通过变更变量和 `LTExpression` 和 `EQExpression` 再增加终止性判断的后置条件。前者是严格小于，后者是用于多于一项秩函数时判断字典序下降序列

      - `List<Expression> wp_list` 表示部分正确性后置条件列表
      - `List<List<Expression>> ckl` 表示终止性后置条件列表

   4. 过程程序的验证是从后往前的，所以实现的时候也就是从最后一个 Basic Block 的最后一个 Expression 开始推导。Block 里面一共有5种Statement：

      1.  VariableAssignStatement：对后置条件列表里面的Expression进行变量替换

         `exp = exp.Substitute(VA_s.variable, VA_s.rhs);`

      2. AssumeStatement：将每个后置条件增加蕴含关系

         `exp = new ImplicationExpression(Assume_s.condition, exp);`

      3. AssertStatement：增加新的后置条件

         `wp_list.Add(Assert_s.pred);`

      4. FunctionCallStatement：

         已知，每个路径中，如果存在 `FunctionCall` 的话，当前路径数量至少+1

         - 新路径：增加新的后置条件：被调用的函数的前置条件为新路径；检查是否存在秩函数，如果存在的话就再增加一个新路径
         - 原路径：
           1. 对原后置条件进行变量替换
           2. 增加Assume

      5. SubscriptAssignStatement：对后置条件列表里面的Expression进行变量替换

   5. 对于普通的后置条件列表里的后置条件，检查 `Expression check_wp = new ImplicationExpression(当前路径的前置条件, 后置条件);` 是否有效

   6. 对于终止性后置条件列表里的后置条件

      - 先把变量替换回来
      - 如果只有一个后置条件，直接判断是否严格小于
      - 多于一个后置条件，按照字典序下降检查

## 困难和解决方法：

1. 对路径的理解存在错误，一开始直接从后置条件开始往前替换，忽略了路径的起点不只是前置条件块，也包括循环头。解决方法：使用路径搜索方法，把根据块连接的路径找出来，再根据每个块里面的Statement增加其他分支。
2. 对于`FunctionCallStatement`的处理不熟练，出现了很多小bug。解决方法：逐步拆分函数调用后需要进行的操作，包括：（1）替换变量为输入的参数；（2）对已有的每个后置条件增加Assume；（3）根据调用函数增加新的普通后置函数路径；（4）判断是否存在秩函数，如果是，增加新的秩函数后置条件路径。