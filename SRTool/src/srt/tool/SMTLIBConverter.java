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

        // Adds the variable names
        for (String currentVariable : variableNames) {
            prog += "(declare-fun " + currentVariable + " () (_ BitVec 32))\n";

        }

        // Visits the expression lists
        exprConverter = new ExprToSmtlibVisitor();
        for (Expr exp : transitionExprs) {
            prog += "(assert " + exprConverter.visit(exp) + ")\n";

        }

        // Visits the propertyExpr's
        prog += "(assert (not ";
        prog += generatePropertyFormula(propertyExprs,0);
        prog += ") ) ";


        query = new StringBuilder(prog);
        //query = new StringBuilder("(set-logic QF_BV)\n" +
        //		"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
        // TODO: Define more functions above (for convenience), as needed.

        // TODO: Declare variables, add constraints, add properties to check
        // here.


        query.append("(check-sat)\n");

    }

    /* Function to generate the formula for assertion properties
     * @param propertyExprs - the list of property expressions
     * @param index         - the current index we are considering in propertyExprs
     */
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
