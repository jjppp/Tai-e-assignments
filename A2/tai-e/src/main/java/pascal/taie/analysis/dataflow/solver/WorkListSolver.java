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

package pascal.taie.analysis.dataflow.solver;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.function.Predicate;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> queue = new LinkedList<>();
        HashSet<Node> vis = new HashSet<>();
        for (var x : cfg) {
            queue.add(x);
            vis.add(x);
        }
        while (!queue.isEmpty()) {
            Node front = queue.remove();
            vis.remove(front);
            Fact outFact = result.getOutFact(front);
            Fact inFact = result.getInFact(front);
            for (var predecessor : cfg.getPredsOf(front)) {
                analysis.meetInto(result.getOutFact(predecessor), inFact);
            }
            result.setInFact(front, inFact);
            if (!analysis.transferNode(front, inFact, outFact)) {
                continue;
            }
            result.setOutFact(front, outFact);
            cfg.getSuccsOf(front).stream()
                    .filter(Predicate.not(vis::contains))
                    .forEach(node -> {
                        queue.add(node);
                        vis.add(node);
                    });
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
