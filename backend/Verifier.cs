/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System;
using System.IO;
using System.Collections.Generic;
using System.Collections;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }


        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>


        public List<List<Block>> dfs_routine(Block root)
        {
            Stack<Block> nodeStack = new Stack<Block>();
            Stack<List<Block>> pathStack = new Stack<List<Block>>();
            List<List<Block>> result = new List<List<Block>>();
            nodeStack.Push(root);
            List<Block> arrayList = new List<Block>();
            arrayList.Add(root);
            pathStack.Push(arrayList);

            while(nodeStack.Count!=0)
            {
                Block curBlock = nodeStack.Pop();
                List<Block> curPath = pathStack.Pop();

                foreach(Block block in curBlock.successors)
                {
                    if(block is not BasicBlock)
                    {
                        List<Block> list = new List<Block>(curPath);
                        list.Add(block);
                        result.Add(list);
                    }
                    else
                    {
                        nodeStack.Push(block);
                        List<Block> list = new List<Block>(curPath);
                        list.Add(block);
                        pathStack.Push(list);                        
                    }
                }
            }
            return result;
        }

        public bool check_ranking(Function function)
        {
            Expression t = new BoolConstantExpression(true);
            Expression r = new BoolConstantExpression(true);
            foreach(Expression exp in function.preconditionBlock.conditions)
            {
                t = new AndExpression(t, exp);
            }
            foreach(Expression exp in function.preconditionBlock.rankingFunctions)
            {
                Expression c = new LEExpression(new IntConstantExpression(0), exp);
                r = new AndExpression(r, c);
            }
            Expression ck = new ImplicationExpression(t, r);
            if(solver.CheckValid(ck)!=null)
            {
                return false;
            }
            foreach(Block block in function.blocks)
            {
                if(block is LoopHeadBlock hb)
                {
                    Expression tt = new BoolConstantExpression(true);
                    Expression rr = new BoolConstantExpression(true);
                    foreach(Expression exp in hb.invariants)
                    {
                        tt = new AndExpression(tt, exp);
                    }
                    foreach(Expression exp in hb.rankingFunctions)
                    {
                        Expression cc = new LEExpression(new IntConstantExpression(0), exp);
                        rr = new AndExpression(rr, cc);
                    }
                    Expression cck = new ImplicationExpression(tt, rr);
                    if(solver.CheckValid(cck)!=null)
                    {
                        return false;
                    }
                }
            }
            return true;
        }


        public int Apply(IRMain cfg)
        {
            if(cfg.predicates.First!=null)
            {
                LinkedListNode<Predicate> predicate = cfg.predicates.First;
                while(true)
                {
                    solver.definePredicate(predicate.Value);
                    if(predicate.Next!=null)
                    {
                        predicate = predicate.Next;
                    }
                    else
                    {
                        break;
                    }
                }
            }
            
            foreach(Function func in cfg.functions)
            {
                if(check_ranking(func) == false)
                {
                    return -1;
                }
            }
            
            List<List<Block>> res = new List<List<Block>>();
            foreach(Function func in cfg.functions)
            {
                List<List<Block>> res1 = dfs_routine(func.preconditionBlock);
                foreach(List<Block> a in res1)
                {
                    res.Add(a);
                }

                foreach(Block block in func.blocks)
                {
                    if(block is not BasicBlock)
                    {
                        List<List<Block>> res2 = dfs_routine(block);
                        foreach(List<Block> res_ in res2)
                        {
                            res.Add(res_);
                        }
                    }
                }
            }
            foreach(List<Block> lisblk in res)
            {
                Expression wp = new BoolConstantExpression(true);

                Block post_blk = lisblk[lisblk.Count-1];

                Block pre_blk = lisblk[0];

                if(post_blk is PostconditionBlock postb)
                {
                    if(postb.conditions.Count>1)
                    {
                        wp = postb.conditions[0];
                        for(int k = 1; k < postb.conditions.Count; k++)
                        {
                            wp = new AndExpression(wp, postb.conditions[k]);
                        }
                    }
                    else if(postb.conditions.Count==1)
                    {
                        wp = postb.conditions[0];
                    }
                }
                else if(post_blk is LoopHeadBlock lhb)
                {

                    if(lhb.invariants.Count>1)
                    {
                        wp = lhb.invariants[0];
                        for(int k = 1; k < lhb.invariants.Count; k++)
                        {
                            wp = new AndExpression(wp, lhb.invariants[k]);
                        }
                    }
                    else if(lhb.invariants.Count==1)
                    {
                        wp = lhb.invariants[0];
                    }
                }
                Expression cur_pred = new BoolConstantExpression(true);

                if(pre_blk is PreconditionBlock preb)
                {
                    if(preb.conditions.Count>1)
                    {
                        cur_pred = preb.conditions[0];
                        for(int k = 1; k < preb.conditions.Count; k++)
                        {
                            cur_pred = new AndExpression(cur_pred, preb.conditions[k]);
                        }
                    }
                    else if(preb.conditions.Count==1)
                    {
                        cur_pred = preb.conditions[0];
                    }
                }
                else if(pre_blk is LoopHeadBlock lhb)
                {
                    if(lhb.invariants.Count>1)
                    {
                        cur_pred = lhb.invariants[0];
                        for(int k = 1; k < lhb.invariants.Count; k++)
                        {
                            cur_pred = new AndExpression(cur_pred, lhb.invariants[k]);
                        }
                    }
                    else if(lhb.invariants.Count==1)
                    {
                        cur_pred = lhb.invariants[0];                    
                    }
                }

                List<Expression> wp_list = new List<Expression>();
                List<List<Expression>> ckl = new List<List<Expression>>();
                List<LocalVariable> fv = new List<LocalVariable>();
                List<LocalVariable> fv1 = new List<LocalVariable>();
                
                if(pre_blk is HeadBlock shb && post_blk is HeadBlock ehb)
                {
                    if(shb.rankingFunctions.Count==ehb.rankingFunctions.Count && shb.rankingFunctions.Count!=0)
                    {
                        List<Expression> clo = new List<Expression>();
                        Expression new_wp = new BoolConstantExpression(true);
                        for(int jdx = 0; jdx < shb.rankingFunctions.Count; jdx++)
                        {
                            Expression exp = shb.rankingFunctions[jdx];
                            foreach(LocalVariable lv in exp.GetFreeVariables())
                            {
                                fv.Add(lv);
                                LocalVariable lv_new = new LocalVariable
                                {
                                name = lv.name + "'"+ fv.Count,
                                type = lv.type  
                                };
                                fv1.Add(lv_new);
                                exp = exp.Substitute(lv, new VariableExpression(lv_new));
                            }
                           
                            if(jdx==0)
                            {
                                new_wp = new LTExpression(ehb.rankingFunctions[jdx], exp);
                                clo.Add(new_wp);
                                new_wp = new EQExpression(ehb.rankingFunctions[jdx], exp);
                                clo.Add(new_wp);
                            }
                            else
                            {
                                Expression t_exp = new LTExpression(ehb.rankingFunctions[jdx], exp);
                                clo.Add(t_exp);
                                t_exp = new EQExpression(ehb.rankingFunctions[jdx], exp);
                                clo.Add(t_exp);
                            }

                            
                        }
                        ckl.Add(clo);
                    }
                }

                
                wp_list.Add(wp);

                for(int k = lisblk.Count-2; k>=0; k--)
                {
                    if(k==0 && lisblk[k] is not LoopHeadBlock)
                    {
                        break;
                    }
                    Block curBlock = lisblk[k];

                    if(curBlock.statements.Last is not null)
                    {
                        LinkedListNode<Statement> node = curBlock.statements.Last;
                        for(int idx = 0; idx < curBlock.statements.Count; idx++)
                        {
                            Statement curStat = node.Value;

                            if(curStat is VariableAssignStatement VA_s)
                            {
                                for(int idx_i = 0; idx_i < wp_list.Count; idx_i++)
                                {
                                    Expression exp = wp_list[idx_i];
                                    exp = exp.Substitute(VA_s.variable, VA_s.rhs);
                                    wp_list[idx_i] = exp;
                                }

                                for(int index = 0; index < ckl.Count; index++)
                                {
                                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                                    {
                                        ckl[index][jdx] = ckl[index][jdx].Substitute(VA_s.variable, VA_s.rhs);
                                    }
                                }


                                if(node.Previous is not null)
                                {
                                    node = node.Previous;
                                }
                            }
                            else if(curStat is AssumeStatement Assume_s)
                            {
                                for(int idx_i = 0; idx_i < wp_list.Count; idx_i++)
                                {
                                    Expression exp = wp_list[idx_i];
                                    exp = new ImplicationExpression(Assume_s.condition, exp);

                                    wp_list[idx_i] = exp;
                                }

                                for(int index = 0; index < ckl.Count; index++)
                                {
                                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                                    {
                                        ckl[index][jdx] = new ImplicationExpression(Assume_s.condition, ckl[index][jdx]);
                                    }
                                }

                                if(node.Previous is not null)
                                {
                                    node = node.Previous;
                                }

                            }
                            else if(curStat is AssertStatement Assert_s)
                            {
                                wp_list.Add(Assert_s.pred);

                                if(node.Previous is not null)
                                {
                                    node = node.Previous;
                                }
                            }
                            else if(curStat is FunctionCallStatement FC_s)
                            {
                                List<LocalVariable> lhs = FC_s.lhs;
                                FunctionCallExpression rhs = FC_s.rhs;
                                Function function = rhs.function;
                                List<LocalVariable> argumentVariables = rhs.argumentVariables;
                                List<LocalVariable> parameters = function.parameters;
                                List<Expression> Post_conditions = function.postconditionBlock.conditions;
                                List<Expression> Pred_conditions = function.preconditionBlock.conditions;
                                List<LocalVariable> rvs = function.rvs;
                                List<Expression> rvs_exp = new List<Expression>();
                                List<Expression> ranking_func = new List<Expression>(function.preconditionBlock.rankingFunctions.ToArray());
                                if(lhs.Count != rvs.Count)
                                {
                                    return -1;
                                }

                                for(int index = 0; index < rvs.Count; index++)
                                {
                                    Expression rvs_ = new VariableExpression(rvs[index]);
                                    rvs_exp.Add(rvs_);
                                }

                                for(int index = 0; index < rvs_exp.Count; index++)
                                {
                                    for(int m = 0; m < parameters.Count; m++)
                                    {
                                        Expression ve = new VariableExpression(argumentVariables[m]);
                                        rvs_exp[index] = rvs_exp[index].Substitute(parameters[m], ve);
                                    }
                                }

                                for(int index = 0; index < wp_list.Count; index++)
                                {
                                    for(int m = 0; m < rvs_exp.Count; m++)
                                    {
                                        wp_list[index] = wp_list[index].Substitute(lhs[m], rvs_exp[m]);
                                    }
                                }

                                for(int index = 0; index < ckl.Count; index++)
                                {
                                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                                    {
                                        for(int m = 0; m < rvs_exp.Count; m++)
                                        {
                                            ckl[index][jdx] = ckl[index][jdx].Substitute(lhs[m], rvs_exp[m]);
                                        }
                                        
                                    }
                                }


                                Expression Post_exp = new BoolConstantExpression(true);
                                if(Post_conditions.Count > 1)
                                {
                                    Post_exp = Post_conditions[0];
                                    for(int key = 0; key < Post_conditions.Count; key++)
                                    {
                                        Post_exp = new AndExpression(Post_exp, Post_conditions[key]);
                                    }
                                }
                                else if(Post_conditions.Count == 1)
                                {
                                    Post_exp = Post_conditions[0];
                                }

                                for(int index = 0; index < parameters.Count; index++)
                                {
                                    Expression ve = new VariableExpression(argumentVariables[index]);
                                    Post_exp = Post_exp.Substitute(parameters[index], ve);
                                }


                                for(int index = 0; index < wp_list.Count; index++)
                                {
                                    wp_list[index] = new ImplicationExpression(Post_exp, wp_list[index]);

                                }

                                for(int index = 0; index < ckl.Count; index++)
                                {
                                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                                    {
                                        ckl[index][jdx] = new ImplicationExpression(Post_exp, ckl[index][jdx]);
                                    }
                                }

                                Expression Pred_exp = new BoolConstantExpression(false);
                                if(Pred_conditions.Count > 1)
                                {
                                    Pred_exp = Pred_conditions[0];
                                    for(int key = 0; key < Pred_conditions.Count; key++)
                                    {
                                        Pred_exp = new AndExpression(Pred_exp, Pred_conditions[key]);
                                    }
                                }
                                else if(Pred_conditions.Count == 1)
                                {
                                    Pred_exp = Pred_conditions[0];
                                }

                                for(int index = 0; index < parameters.Count; index++)
                                {
                                    Expression ve = new VariableExpression(argumentVariables[index]);
                                    Pred_exp = Pred_exp.Substitute(parameters[index], ve);
                                }

                                wp_list.Add(Pred_exp);

                                for(int index = 0; index < parameters.Count; index++)
                                {
                                    for(int num = 0; num < ranking_func.Count; num++)
                                    {
                                        ranking_func[num] = ranking_func[num].Substitute(parameters[index], new VariableExpression(argumentVariables[index]));
                                    }
                                }

                                if(pre_blk is HeadBlock phb && phb.rankingFunctions.Count==ranking_func.Count && ranking_func.Count!=0)
                                {
                                    List<Expression> clo = new List<Expression>();
                                    Expression new_wp = new BoolConstantExpression(true);
                                    for(int j = 0; j < phb.rankingFunctions.Count; j++)
                                    {
                                        Expression exp = phb.rankingFunctions[j];
                                        foreach(LocalVariable lv in exp.GetFreeVariables())
                                        {
                                            fv.Add(lv);
                                            LocalVariable lv_new = new LocalVariable
                                            {
                                                name = lv.name + "'" + fv.Count,
                                                type = lv.type
                                            };
                                            fv1.Add(lv_new);
                                            exp = exp.Substitute(lv, new VariableExpression(lv_new));
                                        }
                                        if(j==0)
                                        {
                                            new_wp = new LTExpression(ranking_func[j], exp);
                                            clo.Add(new_wp);
                                            new_wp = new EQExpression(ranking_func[j], exp);
                                            clo.Add(new_wp);
                                        }
                                        else
                                        {
                                            Expression t_exp = new LTExpression(ranking_func[j], exp);
                                            clo.Add(t_exp);
                                            t_exp = new EQExpression(ranking_func[j], exp);
                                            clo.Add(t_exp);
                                        }
                                    }
                                    ckl.Add(clo);
                                }

                                if(node.Previous is not null)
                                {
                                    node = node.Previous;
                                }
                            }
                            else if(curStat is SubscriptAssignStatement SA_s)
                            {
                                VariableExpression array = new VariableExpression(SA_s.array);
                                VariableExpression arraylen = new VariableExpression(SA_s.array.length);
                                ArrayUpdateExpression expr = new ArrayUpdateExpression(array, SA_s.subscript, SA_s.rhs, arraylen);

                                for(int index = 0; index < wp_list.Count; index++)
                                {
                                    wp_list[index] = wp_list[index].Substitute(SA_s.array, expr);
                                }

                                for(int index = 0; index < ckl.Count; index++)
                                {
                                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                                    {
                                        ckl[index][jdx] = ckl[index][jdx].Substitute(SA_s.array, expr);
                                    }
                                }
                                if(node.Previous is not null)
                                {
                                    node = node.Previous;
                                }
                            }
                        }
                    }
                }


                for(int index = 0; index < ckl.Count; index++)
                {
                    for(int jdx = 0; jdx < ckl[index].Count; jdx++)
                    {
                        for(int n = 0; n < fv.Count; n++)
                        {
                            ckl[index][jdx] = ckl[index][jdx].Substitute(fv1[n], new VariableExpression(fv[n]));
                        }
                    }
                }

                foreach(Expression _wp in wp_list)
                {
                    Expression check_wp = new ImplicationExpression(cur_pred, _wp);

                    if(solver.CheckValid(check_wp)!=null)
                    {
                        return -1;
                    }
                }
                

                foreach(List<Expression> le in ckl)
                {
                    int ln = 0;
                    while(ln < le.Count)
                    {
                        Expression check_1 = new ImplicationExpression(cur_pred, le[ln]);
                        Expression check_2 = new ImplicationExpression(cur_pred, le[ln+1]);
                        if(solver.CheckValid(check_1)==null)
                        {
                            break;
                        }
                        else if(solver.CheckValid(check_1)!=null && ln+2 >= le.Count)
                        {
                            return -1;
                        }
                        else if(solver.CheckValid(check_1)!=null && solver.CheckValid(check_2)==null)
                        {
                            ln += 2;
                        }
                        else if(solver.CheckValid(check_1)!=null && solver.CheckValid(check_2)!=null)
                        {
                            return -1;
                        }
                    }
                }
            }

            return 1;
        }
    }
}