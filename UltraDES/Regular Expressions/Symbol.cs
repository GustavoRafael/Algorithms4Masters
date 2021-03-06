////////////////////////////////////////////////////////////////////////////////////////////////////
// file:	Regular Expressions\Symbol.cs
//
// summary:	Implements the symbol class
////////////////////////////////////////////////////////////////////////////////////////////////////

using System;

namespace UltraDES
{
    ////////////////////////////////////////////////////////////////////////////////////////////////////
    /// <summary>   (Serializable)a symbol. </summary>
    ///
    /// <remarks>   Lucas Alves, 15/01/2016. </remarks>
    ////////////////////////////////////////////////////////////////////////////////////////////////////

    [Serializable]
    public abstract class Symbol : RegularExpression
    {
        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Gets the step simplify. </summary>
        ///
        /// <value> The step simplify. </value>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public override RegularExpression StepSimplify
        {
            get { return this; }
        }

        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Gets the epsilon. </summary>
        ///
        /// <value> The epsilon. </value>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public static Symbol Epsilon { 
            get{
                return UltraDES.Epsilon.EpsilonEvent;
            }
        }

        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Gets the empty. </summary>
        ///
        /// <value> The empty. </value>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public static Symbol Empty
        {
            get
            {
                return UltraDES.Empty.EmptyEvent;
            }
        }

        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Returns a string that represents the current object. </summary>
        ///
        /// <remarks>   Lucas Alves, 15/01/2016. </remarks>
        ///
        /// <returns>   A string that represents the current object. </returns>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public abstract override string ToString();

        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Serves as the default hash function. </summary>
        ///
        /// <remarks>   Lucas Alves, 15/01/2016. </remarks>
        ///
        /// <returns>   A hash code for the current object. </returns>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public abstract override int GetHashCode();

        ////////////////////////////////////////////////////////////////////////////////////////////////////
        /// <summary>   Determines whether the specified object is equal to the current object. </summary>
        ///
        /// <remarks>   Lucas Alves, 15/01/2016. </remarks>
        ///
        /// <param name="obj">  The object to compare with the current object. </param>
        ///
        /// <returns>
        ///     true if the specified object  is equal to the current object; otherwise, false.
        /// </returns>
        ////////////////////////////////////////////////////////////////////////////////////////////////////

        public abstract override bool Equals(object obj);
    }
}