package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import srt.ast.Expr;

public class SMTLIBConverter {

    private ExprToSmtlibVisitor exprConverter;
    private StringBuilder query;

    public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {

        if(propertyExprs.size() == 0)
        {
            throw new IllegalArgumentException("No assertions.");
        }
        // Create a StringBuilder with a decent amount of memory
        query = new StringBuilder(10);

        // Initialise expression to SMT-LIB converter
        exprConverter = new ExprToSmtlibVisitor();

        // Start building the query string
        query.append( "(set-logic QF_BV)\n");
        query.append( "(declare-fun main() Bool)\n");

        // Function to convert a boolean to a bitvector of length 32 of either all 1's or all 0's
        query.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");

        // Function to take a bit vector of length 32 and returns a bool
        // @result false if the input is all zeros
        // @result true otherwise
        query.append("(define-fun tobool ((p (_ BitVec 32))) (Bool) (not (= p (_ bv0 32))))\n");

        generateVariableNames(variableNames);

        generateVariablesForProperties(propertyExprs);

        generateTransitionExpressions(transitionExprs);

        // Recursively generate all the properties to represent assertion
        query.append(generatePropertyPredicates(propertyExprs,0));

        // Recursively generate the final assertion
        query.append("(assert (not ");
        query.append(generatePropertyFormula(propertyExprs,0));
        query.append( ") )");

        // Execute the query
        query.append("(check-sat)\n");

        // Get the values for the properties as the result
        query.append("(get-value (");
        for (int i = 0; i < propertyExprs.size(); i++) {
            query.append("prop" + i + " ");
        }
        query.append("))");

        // Uncomment to print out the SMT-LIB syntax
        // System.out.println(query.toString());
    }

    // Convert variable names to SMT-LIB syntax
    private void generateVariableNames(Set<String> variableNames ) {
        for (String currentVariable : variableNames) {
            query.append( "(declare-fun " + currentVariable + " () (_ BitVec 32))\n");
        }
    }

    // Generate names for all the properties that will be used in the end.
    private void generateVariablesForProperties(List<Expr> propertyExprs) {
        for (int i = 0; i < propertyExprs.size(); i++) {
            query.append("(declare-fun prop" + i + " () (Bool))\n");
        }
    }

    // Convert transition expressions to SMT-LIB syntax
    private void generateTransitionExpressions(List<Expr> transitionExprs) {
        for (Expr exp : transitionExprs) {
            query.append( "(assert (tobool " + exprConverter.visit(exp) + "))\n");
        }
    }

    // Recursively generate all the properties to represent assertion
    private String generatePropertyPredicates(List<Expr> propertyExprs, int index) {
            if (index == propertyExprs.size()) return "";
            return "(assert (= prop" + index + " (tobool " + exprConverter.visit(propertyExprs.get(index)) + ")))\n" + generatePropertyPredicates(propertyExprs, index+1);
    }

    // Recursively generate the final assertion
    private String generatePropertyFormula(List<Expr> propertyExprs, int index) {
         if (index == propertyExprs.size() - 1) {
            return  "prop" + index;
         }
         return "(and prop" + index +  " " + generatePropertyFormula(propertyExprs, index+1) + ")";
    }

    public String getQuery() {
        return query.toString();
    }
}
