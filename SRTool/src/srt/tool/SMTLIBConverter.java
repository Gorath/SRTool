package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {

    private ExprToSmtlibVisitor exprConverter;
    private StringBuilder query;

    public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {

        if(propertyExprs.size() == 0)
        {
            throw new IllegalArgumentException("No assertions.");
        }

        String prog = "(set-logic QF_BV)\n";
        prog += "(declare-fun main() Bool)\n";
        prog += "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";
        //prog += "(define-fun bvee ((ba BitVec 32)(bb BitVec 32)) Bool (and (bvsge ba bb) (bvsle ba bb)))\n";

        // Convert variable names to SMT-LIB syntax
        prog += generateVariableNames(variableNames);

        exprConverter = new ExprToSmtlibVisitor();

        // Convert transition expressions to SMT-LIB syntax
        prog += generateTransitionExpressions(transitionExprs);

        // Convert property expressions to SMT-LIB syntax
        prog += "(assert (not ";
        prog += generatePropertyFormula(propertyExprs,0);
        prog += ") ) ";

        System.out.println(prog);

        query = new StringBuilder(prog);
        // TODO: Declare variables, add constraints, add properties to check
        // here.

        query.append("(check-sat)\n");
    }

    private String generateVariableNames(Set<String> variableNames) {
        String newVariableNames = "";
        for (String currentVariable : variableNames) {
            newVariableNames += "(declare-fun " + currentVariable + " () (_ BitVec 32))\n";
        }
        return newVariableNames;
    }

    private String generateTransitionExpressions(List<Expr> transitionExprs) {
        String newTransitionExprs = "";
        for (Expr exp : transitionExprs) {
            newTransitionExprs += "(assert " + exprConverter.visit(exp) + ")\n";

        }
        return newTransitionExprs;
    }

    private String generatePropertyFormula(List<Expr> propertyExprs, int index) {
         if (index == propertyExprs.size() - 1) {
            return  exprConverter.visit(propertyExprs.get(index));
         }
         return  "(and " + exprConverter.visit(propertyExprs.get(index)) +" " + generatePropertyFormula(propertyExprs, index+1) + ")";
    }

    public String getQuery() {
        return query.toString();
    }

    public List<Integer> getPropertiesThatFailed(String queryResult) {
        List<Integer> res = new ArrayList<Integer>();

        return res;
    }

}
