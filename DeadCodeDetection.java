/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        ArrayDeque<Stmt> st = new ArrayDeque<>();
        Set<Stmt> re = new HashSet<>();
        Set<Stmt> reached = new HashSet<>();
        st.addLast(cfg.getEntry());
        re.add(cfg.getExit());
        re.add(cfg.getEntry());
        while(!st.isEmpty()) {
            Stmt s = st.pollFirst();
            reached.add(s);
            if(s instanceof AssignStmt assignStmt) {
                SetFact<Var> le=liveVars.getResult(assignStmt);
                LValue lValue = assignStmt.getLValue();
                RValue rValue = assignStmt.getRValue();
                boolean f=true;
                if(lValue instanceof Var) {
                    if (!le.contains((Var) lValue)) {
                        if (hasNoSideEffect(rValue)) {
                            f = false;
                        }
                    }
                }
                if (f) {
                    re.add(assignStmt);
                }
                for (Stmt succ : cfg.getSuccsOf(assignStmt)) {
                    if (!reached.contains(succ))
                        st.addLast(succ);
                }
            }
            else if(s instanceof If ifStmt) {
                CPFact result = constants.getResult(ifStmt);
                ConditionExp condition = ifStmt.getCondition();
                ConditionExp.Op operator = condition.getOperator();
                Value evaluate = ConstantPropagation.evaluate(condition, result);
                re.add(ifStmt);
                if (evaluate.isConstant()) {
                    if (evaluate.getConstant() == 1) {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt)) {
                            if (edge.getKind() == Edge.Kind.IF_TRUE) {
                                Stmt target = edge.getTarget();
                                if (!reached.contains(target))
                                    st.add(target);
                            }
                        }
                    } else {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(s)) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                Stmt target = edge.getTarget();
                                if (!reached.contains(target))
                                    st.add(target);
                            }
                        }
                    }
                }
                else {
                    for (Stmt succ : cfg.getSuccsOf(s)) {
                        if (!reached.contains(succ))
                            st.addLast(succ);
                    }
                }
            }else if (s instanceof SwitchStmt switchStmt){
                Var var = switchStmt.getVar();
                CPFact result = constants.getResult(switchStmt);
                re.add(switchStmt);
                if (result.get(var).isConstant()) {
                    int constant = result.get(var).getConstant();
                    boolean match = false;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                            int caseValue = edge.getCaseValue();
                            if (caseValue == constant) {
                                match = true;
                                if (!reached.contains(edge.getTarget()))
                                    st.addLast(edge.getTarget());
                            }
                        }
                    }
                    if (!match) {
                        Stmt defaultTarget = switchStmt.getDefaultTarget();
                        if (!reached.contains(defaultTarget))
                            st.addLast(defaultTarget);
                    }
                } else {
                    for (Stmt succ : cfg.getSuccsOf(switchStmt)) {
                        if (!reached.contains(succ))
                            st.addLast(succ);
                    }
                }
            }else {
                re.add(s);
                for (Stmt succ : cfg.getSuccsOf(s)) {
                    if (!reached.contains(succ))
                        st.addLast(succ);
                }
            }
        }
        for (Stmt stmt : ir.getStmts()) {
            if (!re.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
