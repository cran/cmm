\name{SpecifyCoefficient}
\alias{SpecifyCoefficient}
\title{SpecifyCoefficient}

\description{Gives the generalized exp-log specification for various coefficients}

\usage{SpecifyCoefficient(name, arg = NULL, rep = 1, data = NULL)}

\arguments{
\item{name}{character: name of desired coefficient}
\item{arg}{an argument specific to the coefficient, e.g., a vector of scores or number of rows and colums. }
\item{data}{data set. Necessary for MEL estimation}
\item{rep}{number of repetitions of the coefficient}
}

\details{
Currently the following coefficients are implemented:

\preformatted{
 SpecifyCoefficient("Mean",arg = scores)
 SpecifyCoefficient("Variance", arg = scores)
 SpecifyCoefficient("StandardDeviation", arg = scores)
 SpecifyCoefficient("GiniMeanDifference", arg = scores)
 SpecifyCoefficient("Entropy", arg = k)
 SpecifyCoefficient("DiversityIndex", arg = k)
 SpecifyCoefficient("Covariance",arg = list(xscores,yscores))
 SpecifyCoefficient("Correlation",arg = list(xscores,yscores))
 SpecifyCoefficient("KendallTau",arg = list(r,c))
 SpecifyCoefficient("GoodmanKruskalGammma",arg = list(r,c))
 SpecifyCoefficient("CohenKappa",r)
 SpecifyCoefficient("CronbachAlpha",arg = list(items,item.scores), data = X) 
 SpecifyCoefficient("Hij")
 SpecifyCoefficient("DifferenceInProportions",arg = m)
 SpecifyCoefficient("LogOddsRatio")
 SpecifyCoefficient("LoglinearParameters",arg = dim)
 SpecifyCoefficient("Probabilities",arg = dim)
 SpecifyCoefficient("LogProbabilities",arg = dim)
 SpecifyCoefficient("ConditionalProbabilities",arg = list(var,condvar,dim))
 SpecifyCoefficient("AllMokkenHj", arg = list(items,item.scores), data = X)
 SpecifyCoefficient("MokkenH", arg = list(items,item.scores), data = X)
 SpecifyCoefficient("OrdinalLocation-A", arg = arg)
 SpecifyCoefficient("OrdinalLocation-L", arg = arg)
 SpecifyCoefficient("OrdinalDispersion-A", arg = arg)
 SpecifyCoefficient("OrdinalDispersion-L", arg = arg)
}


Here,  \code{scores} is a score vector, e.g., \code{c(1,2,3,4,5)}; \code{k} is the number of cells in a table;
\code{r} is the number of rows and columns of a square table; \code{dim} is the dimension of the table; \code{items} are the columns
 in the data matrix that should be used for compuing the statistic; \code{item.scores} is the number of item scores (e.g., 2 for dichotomous items,
 or 5 for Likert items); \code{X} is the NxJ data matrix. \code{"LoglinearParameters"}
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
   SpecifyCoefficient("Mean",arg = c(1,2,3))
   SpecifyCoefficient("Variance",arg = c(1,2,3))
   SpecifyCoefficient("StandardDeviation",arg = c(1,2,3))
   SpecifyCoefficient("GiniMeanDifference",arg = c(1,2,3))
   SpecifyCoefficient("Entropy",arg = 5)
   SpecifyCoefficient("DiversityIndex",arg = 5)
   SpecifyCoefficient("Covariance",arg = list(c(1,2,3),c(1,2,3)))
   SpecifyCoefficient("Correlation",arg = list(c(1,2,3),c(1,2,3)))
   SpecifyCoefficient("KendallTau",arg = list(3,4))
   SpecifyCoefficient("GoodmanKruskalGammma",arg = list(3,4))
   SpecifyCoefficient("CohenKappa",arg = 3)
   SpecifyCoefficient("DifferenceInProportions",arg = 1)
   SpecifyCoefficient("LogOddsRatio",arg = 1)
   SpecifyCoefficient("LoglinearParameters",arg = c(3,3))
   SpecifyCoefficient("Probabilities",arg = 8)
   SpecifyCoefficient("LogProbabilities",arg = 8)
   # conditional probabilities for 3x3 table, conditioning on first variable
   SpecifyCoefficient("ConditionalProbabilities",arg = list(c(1,2),c(1),c(3,3)))
}

\keyword{univar}
