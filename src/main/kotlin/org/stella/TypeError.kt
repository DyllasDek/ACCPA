package org.stella

import StellaTypeException
import org.syntax.stella.Absyn.Match
import org.syntax.stella.Absyn.Type
import org.syntax.stella.PrettyPrinter

/**
 * Class for reporting type errors
 * @constructor Create empty Type error out
 *
 */
class TypeErrorOut {

    fun unexpected_access_tuple( num: Int, length: Int, type: Type, where: String) {
        println("TYPE ERROR \n in $where:\n Unexpected access to component $num of the tuple with length $length of type ${PrettyPrinter.print(type)}")
        throw StellaTypeException()
    }
    /**
     * Report expected type and got type
     * @param expc expected type
     * @param got got type
     * @param where where the error occurred
     */
    fun expected_got(expc:Type, got: Type, where: String) {
        println("TYPE ERROR \n in $where:\n Expected ${PrettyPrinter.print(expc)}, got ${PrettyPrinter.print(got)}")
        throw StellaTypeException()
    }

    /**
     * Report too few arguments
     * @param where where the error occurred
     */
    fun few_arguments(where: String) {
        println("TYPE ERROR \n in $where:\n Too few arguments")
        throw StellaTypeException()
    }

    /**
     * Report undefined variable
     */
    fun undefined_variable(stellaident_: Any, s: String) {
        println("TYPE ERROR \n in $s :\n Undefined variable $stellaident_")
        throw StellaTypeException()
    }

    fun match_error(match: Match) {
        println("TYPE ERROR \n in ${PrettyPrinter.print(match)} :\n Branches of match expression have different types")
        throw StellaTypeException()
    }

    fun field_not_found(stellaident_: String?, s: String) {
        println("TYPE ERROR \n in $s :\n Field $stellaident_ not found")
        throw StellaTypeException()
    }

}