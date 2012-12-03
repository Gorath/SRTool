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

        // Start building the query string
        String prog = "(set-logic QF_BV)\n";
        prog += "(declare-fun main() Bool)\n";

        // Function to convert a boolean to a bitvector of length 32 of either all 1's or all 0's
        prog += "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";

        // Function to take a bit vector of length 32 and send back a bool
        // @result false if the input is all zeros
        // @result true otherwise
        prog += "(define-fun tobool ((p (_ BitVec 32))) (Bool) (not (= p (_ bv0 32))))\n";

        // Convert variable names to SMT-LIB syntax
        prog += generateVariableNames(variableNames);

        for (int i = 0; i < propertyExprs.size(); i++) {
            prog += "(declare-fun prop" + i + " () (Bool))\n";
        }

        exprConverter = new ExprToSmtlibVisitor();

        // Convert transition expressions to SMT-LIB syntax
        prog += generateTransitionExpressions(transitionExprs);

        prog += generatePropertyPredicates(propertyExprs,0);

        // Convert property expressions to SMT-LIB syntax
        prog += "(assert (not ";
        prog += generatePropertyFormula(propertyExprs,0);
        prog += ") )";

        // Print out the program (for debugging purposes only)
        System.out.println(prog);


        // Build the query string for the smt solver
        query = new StringBuilder(prog);
        query.append("(check-sat)\n");

        query.append("(get-value (");
        for (int i = 0; i < propertyExprs.size(); i++) {
            query.append("prop" + i + " ");
        }
        query.append("))");

        System.out.println(query.toString());
    }

    private String generatePropertyPredicates(List<Expr> propertyExprs, int index) {
            if (index == propertyExprs.size()) return "";
            return "(assert (= prop" + index + " (tobool " + exprConverter.visit(propertyExprs.get(index)) + ")))\n" + generatePropertyPredicates(propertyExprs, index+1);
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
            newTransitionExprs += "(assert (tobool " + exprConverter.visit(exp) + "))\n";

        }
        return newTransitionExprs;
    }

    private String generatePropertyFormula(List<Expr> propertyExprs, int index) {
         if (index == propertyExprs.size() - 1) {
            return  "prop" + index;
         }
         return "(and prop" + index +  " " + generatePropertyFormula(propertyExprs, index+1) + ")";
    }

    public String getQuery() {
        return query.toString();
    }

    public List<Integer> getPropertiesThatFailed(String queryResult) {
        List<Integer> res = new ArrayList<Integer>();

        ////////////////////////////
        /// Needs changing
        ////////////////////////////
        int i = 9;
        int current = 0;
        while (i < queryResult.length()) {
           if(queryResult.charAt(i) == 't') {
               i+= 12;
            } else {
               i += 13;
               res.add(current);
            }

            current++;
        }

        System.out.println(queryResult);
        return res;
    }

}
