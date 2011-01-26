\name{LaborParticipation}
\alias{LaborParticipation}
\docType{data}
\title{Women's labor participation: 1967-1971}
\description{
The labor participation (yes/no) of 1583 women was measured in five consecutive year, 1967-1971, 
leading to a \eqn{2\times 2\times 2\times 2\times 2}{2 x 2 x 2 x 2 x 2} table.

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, p. 128).

Section 4.3 in Bergsma, Croon and Hagenaars, 2009
}
\usage{data(LaborParticipation)}
\format{
  A data frame with 1583 observations on the following variables.
  \describe{
    \item{\code{Year1967}}{Participated in 1967 (factor):
        1 = No;
        2 = Yes.
       }
    \item{\code{Year1968}}{Participated in 1968 (factor):
        1 = No;
        2 = Yes.
       }
    \item{\code{Year1969}}{Participated in 1969 (factor):
        1 = No;
        2 = Yes.
       }
    \item{\code{Year1970}}{Participated in 1970 (factor):
        1 = No;
        2 = Yes.
       }
    \item{\code{Year1971}}{Participated in 1971 (factor):
        1 = No;
        2 = Yes.
       }
  }
}

\source{
 Heckman & Willis (1977).
}
\references{

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

Heckman, J. J. & Willis, R. J. (1977).
A beta-logistic model for the analysis of sequential labor force participation by married women.
\emph{Journal of Political Economy, 85}, 27-58.

}

\examples{
data(LaborParticipation)
n <- c(t(ftable(LaborParticipation)))

##############################################################################################################
#Sample kappa values

#matrix for obtaining transition matrices for consecutive years
at = MarginalMatrix(c("67","68","69","70","71"),list(c("67","68"),c("68","69"),c("69","70"),c("70","71")),c(2,2,2,2,2));

coeff = SpecifyCoefficient("CohenKappa",arg = 2, rep = 4);
stats = SampleStatistics(n,list(coeff,at),ShowParameters=FALSE)


##############################################################################################################
#Fitting models for kappa
#matrix for obtaining transition matrices for consecutive years
at = MarginalMatrix(c("67","68","69","70","71"),list(c("67","68"),c("68","69"),c("69","70"),c("70","71")),c(2,2,2,2,2));

coeff = SpecifyCoefficient("CohenKappa",2,4);

bt1 = ConstraintMatrix(c(1),c(),c(4)); #equal kappas
bt2 = rbind(c(1,-2,1,0),c(0,1,-2,1));  #linear trend for kappas
model = list(bt1,coeff,at)

m = MarginalModelFit(n,model,ShowParameters=FALSE,ShowProgress=10)

}
\keyword{datasets}
