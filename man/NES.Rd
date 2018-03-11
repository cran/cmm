\name{NES}
\alias{NES}
\docType{data}
\title{Political Orientation in the US, three-wave panel study}
\description{
Data from the US National Election Studies. Three-wave panel study
measuring political orientation on a seven-point scale. The data are
tabulated in Bergsma, Croon, and Hagenaars (2009, 4.4).

Sections 4.2.1 and 4.3 in Bergsma, Croon and Hagenaars (2009).
}
\usage{data(NES)}
\format{
  A data frame with 408 observations on the following variables.
  \describe{
    \item{\code{T1}}{Political orientation at time 1 (ordered):
        1 = Extremely liberal
        2 = Liberal
        3 = Slightly liberal"
        4 = Moderate
        5 = Slightly conservative
        6 = Conservative
        7 = Extremely conservative
       }
    \item{\code{T2}}{Political orientation at time 2 (ordered): see \code{T1}}
    \item{\code{T3}}{Political orientation at time 3 (ordered): see \code{T1}}
  }
}

\source{
US National Election Studies.
}

\references{

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).\emph{Marginal models for dependent, clustered, and longitudinal categorical data.}New York: Springer.

 Examples in book: http://stats.lse.ac.uk/bergsma/cmm/R files/NES.R
}
\examples{
data(NES)

####################################################################################
# Models for marginal homogeneity over time (Section 4.2.1)

# Marginal homogeneity : no change in political orientation over time

at <- MarginalMatrix(c("T1", "T2", "T3"), list(c("T1"), c("T2"), c("T3")), c(7,7,7));
bt1 <- ConstraintMatrix(c("T", "P"), list(c("T"), c("P")), c(3, 7));

model1 <- list(bt1, "identity", at);

start <- c(t(ftable(NES))) + .001;
pihat <- MarginalModelFit(NES, model1,
    MaxSteps = 1000, StartingPoint = start,
    ShowProgress = 100, MaxError = 1e-28,
    CoefficientDimensions = c(3,7), ShowCoefficients = TRUE,
    ShowParameters = FALSE, Labels = c("T", "P"));
}

\keyword{datasets}
