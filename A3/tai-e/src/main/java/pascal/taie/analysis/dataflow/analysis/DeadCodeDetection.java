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
import java.util.function.Predicate;

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
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> visited = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        while (!queue.isEmpty()) {
            var node = queue.remove();
            // CFG reachable nodes
            if (visited.contains(node)) {
                continue;
            }
            visited.add(node);
            if (isDeadAssign(node, liveVars)) {
                deadCode.add(node);
            }
            if (node instanceof If ifStmt) {
                Value cpVal = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getOutFact(node));
                if (cpVal != null && cpVal.isConstant()) {
                    for (var edge : cfg.getOutEdgesOf(node)) {
                        if (edge.getKind() == Edge.Kind.IF_TRUE && cpVal.getConstant() == 1) {
                            queue.add(edge.getTarget());
                        } else if (edge.getKind() == Edge.Kind.IF_FALSE && cpVal.getConstant() == 0) {
                            queue.add(edge.getTarget());
                        }
                    }
                } else {
                    queue.addAll(cfg.getSuccsOf(node));
                }
            } else if (node instanceof SwitchStmt switchStmt) {
                Value cpVal = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getOutFact(node));
                if (cpVal != null && cpVal.isConstant()) {
                    boolean flag = false;
                    for (var edge : cfg.getOutEdgesOf(node)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == cpVal.getConstant()) {
                            queue.add(edge.getTarget());
                            flag = true;
                        }
                    }
                    if (!flag) {
                        queue.add(((SwitchStmt) node).getDefaultTarget());
                    }
                } else {
                    queue.addAll(cfg.getSuccsOf(node));
                }
            } else {
                queue.addAll(cfg.getSuccsOf(node));
            }
        }
        ir.getStmts().stream()
                .filter(Predicate.not(visited::contains))
                .forEach(deadCode::add);
        // Weird workaround
        deadCode.removeIf(stmt -> stmt.getLineNumber() == -1);
        return deadCode;
    }

    private boolean isDeadAssign(Stmt stmt, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (!(stmt instanceof AssignStmt<?, ?> assignStmt)) {
            return false;
        }
        if (!(assignStmt.getLValue() instanceof Var lVar)) {
            return false;
        }
        if (liveVars.getOutFact(stmt).contains(lVar)) {
            return false;
        }
        return hasNoSideEffect(assignStmt.getRValue());
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
