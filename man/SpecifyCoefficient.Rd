\name{SpecifyCoefficient}
\alias{SpecifyCoefficient}
\title{SpecifyCoefficient}

\description{Gives the generalized exp-log specification for various coefficients}

\usage{SpecifyCoefficient(name, arg, rep=1)}

\arguments{
\item{name}{character: name of desired coefficient}
\item{arg}{an argument specific to the coefficient, e.g., a vector of scores or number of rows and colums. }
\item{rep}{number of repetitions of the coefficient}
}

\details{
Currently the following coefficients are implemented:

\preformatted{
 SpecifyCoefficient("Mean",scores)
 SpecifyCoefficient("Variance",scores)
 SpecifyCoefficient("StandardDeviation",scores)
 SpecifyCoefficient("GiniMeanDifference",scores)
 SpecifyCoefficient("Entropy",k)
 SpecifyCoefficient("DiversityIndex",k)
 SpecifyCoefficient("Covariance",list(xscores,yscores))
 SpecifyCoefficient("Correlation",list(xscores,yscores))
 SpecifyCoefficient("KendallTau",list(r,c))
 SpecifyCoefficient("GoodmanKruskalGammma",list(r,c))
 SpecifyCoefficient("CohenKappa",r)
 SpecifyCoefficient("DifferenceInProportions",m)
 SpecifyCoefficient("LogOddsRatio",)
 SpecifyCoefficient("LoglinearParameters",dim)
 SpecifyCoefficient("Probabilities",dim)
 SpecifyCoefficient("LogProbabilities",dim)
 SpecifyCoefficient("ConditionalProbabilities",list(var,condvar,dim))
}

Here,  \code{scores} is a score vector, e.g., \code{c(1,2,3,4,5)}; \code{k} is the number of cells in a table;
\code{r} is the number of rows and columns of a square table; \code{dim} is the dimension of the table. \code{"LoglinearParameters"}
gives the highest order loglinear parameters (loglinear parameters can also be obtained as output of \code{SampleStatistics},
 \code{ModelStatistics} or \code{MarginalModelFit} by setting \code{ShowParameters=TRUE} and the coefficients equal to log probabilities.
}

\value{
 output is of the form \code{list(matlist,funlist)} where \code{matlist} is a list of matrices and \code{funlist} is a list of function names,
 which can currently be \code{"log"}, \code{"exp"}, \code{"identity"}, \code{"xlogx"} (i.e., \eqn{f(x)=x\log(x)}{f(x) = x log(x)}), 
 \code{"xbarx"} (i.e., \eqn{f(x)=x(1-x)}{f(x)=x(1-x)}), \code{"sqrt"}
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{\code{\link{ConstraintMatrix}}, \code{\link{DesignMatrix}}, \code{\link{MarginalMatrix}}
}

\examples{
   SpecifyCoefficient("Mean",c(1,2,3))
   SpecifyCoefficient("Variance",c(1,2,3))
   SpecifyCoefficient("StandardDeviation",c(1,2,3))
   SpecifyCoefficient("GiniMeanDifference",c(1,2,3))
   SpecifyCoefficient("Entropy",5)
   SpecifyCoefficient("DiversityIndex",5)
   SpecifyCoefficient("Covariance",list(c(1,2,3),c(1,2,3)))
   SpecifyCoefficient("Correlation",list(c(1,2,3),c(1,2,3)))
   SpecifyCoefficient("KendallTau",list(3,4))
   SpecifyCoefficient("GoodmanKruskalGammma",list(3,4))
   SpecifyCoefficient("CohenKappa",3)
   SpecifyCoefficient("DifferenceInProportions",1)
   SpecifyCoefficient("LogOddsRatio",1)
   SpecifyCoefficient("LoglinearParameters",c(3,3))
   SpecifyCoefficient("Probabilities",8)
   SpecifyCoefficient("LogProbabilities",8)
   # conditional probabilities for 3x3 table, conditioning on first variable
   SpecifyCoefficient("ConditionalProbabilities",list(c(1,2),c(1),c(3,3)))
}

\keyword{univar}
