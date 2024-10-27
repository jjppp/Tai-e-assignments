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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var fact = new CPFact();
        cfg.getIR().getParams().stream()
                .filter(ConstantPropagation::canHoldInt)
                .forEach(var -> fact.update(var, Value.getNAC()));
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant()
                    ? v1
                    : Value.getNAC();
        } else {
            return v1.isUndef()
                    ? v2
                    : v1;
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = out.copyFrom(in);
        if (!(stmt instanceof DefinitionStmt<?, ?> def)) {
            return changed;
        } else if (def.getLValue() == null || !(def.getLValue() instanceof Var lhs)) {
            return changed;
        } else if (!canHoldInt(lhs)) {
            return changed;
        } else {
            var rhs = def.getRValue();
            changed |= out.update(lhs, evaluate(rhs, in));
            return changed;
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
                default:
                    return false;
            }
        }
        return false;
    }

    private static int boolToInt(boolean b) {
        if (b)
            return 1;
        else
            return 0;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            Value op1 = in.get(((BinaryExp) exp).getOperand1());
            Value op2 = in.get(((BinaryExp) exp).getOperand2());
            if (op2.isConstant() && op2.getConstant() == 0 && exp instanceof ArithmeticExp) {
                if (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV) {
                    return Value.getUndef();
                } else if (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM) {
                    return Value.getUndef();
                }
            }
            if (op1.isConstant() && op2.isConstant()) {
                int val1 = op1.getConstant(), val2 = op2.getConstant();
                if (exp instanceof ArithmeticExp) {
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD:
                            return Value.makeConstant(val1 + val2);
                        case SUB:
                            return Value.makeConstant(val1 - val2);
                        case MUL:
                            return Value.makeConstant(val1 * val2);
                        case DIV: {
                            if (val2 == 0)
                                return Value.getUndef();
                            else
                                return Value.makeConstant(val1 / val2);
                        }
                        case REM: {
                            if (val2 == 0)
                                return Value.getUndef();
                            else
                                return Value.makeConstant(val1 % val2);
                        }
                    }
                } else if (exp instanceof ConditionExp) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case EQ:
                            return Value.makeConstant(boolToInt(val1 == val2));
                        case NE:
                            return Value.makeConstant(boolToInt(val1 != val2));
                        case LT:
                            return Value.makeConstant(boolToInt(val1 < val2));
                        case LE:
                            return Value.makeConstant(boolToInt(val1 <= val2));
                        case GT:
                            return Value.makeConstant(boolToInt(val1 > val2));
                        case GE:
                            return Value.makeConstant(boolToInt(val1 >= val2));
                    }
                } else if (exp instanceof ShiftExp) {
                    switch (((ShiftExp) exp).getOperator()) {
                        case SHL:
                            return Value.makeConstant(val1 << val2);
                        case SHR:
                            return Value.makeConstant(val1 >> val2);
                        case USHR:
                            return Value.makeConstant(val1 >>> val2);
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch (((BitwiseExp) exp).getOperator()) {
                        case AND:
                            return Value.makeConstant(val1 & val2);
                        case OR:
                            return Value.makeConstant(val1 | val2);
                        case XOR:
                            return Value.makeConstant(val1 ^ val2);
                    }
                }
            } else if (op1.isNAC() || op2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
