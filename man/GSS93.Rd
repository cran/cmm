\name{GSS93}
\alias{GSS93}
\docType{data}
\title{Political Orientation and Religion in the United States in 1993 (General Social Survey, 1993)}
\description{
Self-reported Political Orientation (\eqn{P}{P}), Religion (\eqn{R}{R}), and Opinion
of Teenage Birth-control (\eqn{B}{B}) of a sample of 911 US citizens in 1993.
The data stem from the General Social Survey. The data are tabulated
in Bergsma, Croon, and Hagenaars (2009, Table 2.1, Table 2.3).

See Section~2.1 in Bergsma, Croon, and Hagenaars (2009).
}
\usage{data(GSS93)}
\format{
  A data frame with 911 observations on the following three variables.
  \describe{
    \item{\code{P}}{Political orientation (ordered):
        1 = Extremely liberal;
        2 = Liberal;
        3 = Slightly liberal;
        4 = Moderate;
        5 = Slightly conservative;
        6 = Conservative;
        6 = Extremely conservative.
       }
    \item{\code{R}}{Religion (factor):
        1 = Protestant;
        2 = Catholic;
        3 = Other.
       }
    \item{\code{B}}{Opinion of birth control (ordered):
        1 = Strongly agree;
        2 = Agree;
        3 = Disagree;
        4 = Strongly disagree;
       }
  }
}

\source{
 General Social Survey (1993)
}
\references{
 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer

 General Social Survey (1993).
}

\examples{
data(GSS93)

## Table 2.1 of Bergsma, Croon, & Hagenaars (2009)
addmargins(table(GSS93[,1:2]))

## Table 2.2 of Bergsma, Croon, & Hagenaars (2009)
# Specify coefficients
coeff <- list("log",diag(21))
SampleStatistics(GSS93[,1:2],coeff,CoefficientDimensions=c(7,3),Labels=c("P","R"), ShowParameters=TRUE, ShowCoefficients=FALSE)

## Table 2.3 of Bergsma, Croon, & Hagenaars (2009)
ftable(B + R ~ P , data = GSS93)


########################################################
## Models for table PR

#independence of P and R
bt1 = ConstraintMatrix(c("P", "R"), list(c("P"), c("R")), c(7,3));
#linear by nominal model
bt2 = ConstraintMatrix(c("P", "R"), list(c("P","R")), c(7,3), SubsetCoding = list(c("P", "R"),c("Linear", "Nominal")))
#linear by nominal model with equality of first two nominal parameters
bt3 = ConstraintMatrix(c("P", "R"), list(c("P","R")), c(7,3), SubsetCoding = list(c("P", "R"),list("Linear", rbind(c(1,1,0),c(0,0,1)))))
m = MarginalModelFit(GSS93[,1:2],list(bt2,"log"), ShowCoefficients=FALSE, ShowProgress=1, ShowParameters=TRUE, CoefficientDimensions=c(7,3),Labels=c("P","R"),ParameterCoding=list("Polynomial","Effect"))



########################################################
## Models for table PRB

#various loglinear models
bt1 = ConstraintMatrix(c("P", "R","B"), list(c("P","R"),c("B")), c(7,3,4))
bt2 = ConstraintMatrix(c("P", "R","B"), list(c("P","R"),c("R","B")), c(7,3,4))
bt3 = ConstraintMatrix(c("P", "R","B"), list(c("P","R"),c("P","B")), c(7,3,4))
bt4 = ConstraintMatrix(c("P", "R","B"), list(c("P","R"),c("P","B"),c("R","B")), c(7,3,4))
bt5 = ConstraintMatrix(c("P", "R","B"), list(c("P","R"),c("P","B"),c("R","B")), c(7,3,4), SubsetCoding = list(list(c("P", "B"),c("Linear", "Linear")),list(c("R", "B"),c("Nominal", "Linear"))))

m = MarginalModelFit(GSS93,list(bt2,"log"), ShowCoefficients=FALSE, ShowProgress=1, ShowParameters=TRUE,
         CoefficientDimensions=c(7,3,4),Labels=c("P","R","B"), ParameterCoding=list("Polynomial","Polynomial","Effect"))
}
\keyword{datasets}
