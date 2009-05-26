%to do: more examples, comments for examples

\name{DutchPolitics}
\alias{DutchPolitics}
\docType{data}
\title{Political party and candidate preference in the Netherlands}
\description{
The data come from a Dutch panel study (T1 = February 1977, T2 = March 1977) and concern the
questions for which party the respondent intends to vote (variables A and B, respectively) and
which candidate the respondent prefers to become the next Prime Minister (C and D). The data
have been analyzed before (Hagenaars, 1986, 1988, 1990), and more information on the panel
study and the outcomes may be obtained from these references.

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 6.1).
}
\usage{data(DutchPolitics)}
\format{
  A data frame with 1100 observations on the following variables.
  \describe{
    \item{\code{A}}{Party preference at time 1 (factor):
        1 = Christian Democrats;
        2 = Left wing;
        3 = Other.
       }
    \item{\code{B}}{Party preference at time 2 (factor):
        1 = Christian Democrats;
        2 = Left wing;
        3 = Other.
       }
    \item{\code{C}}{Candidate preference at time 1 (factor):
        1 = Christian Democrats;
        2 = Left wing;
        3 = Other.
       }
    \item{\code{D}}{Candidate preference at time 2 (factor):
        1 = Christian Democrats;
        2 = Left wing;
        3 = Other.
       }
  }
}

\source{
J. A. Hagenaars (1990). \emph{Categorical longitudinal data: log-linear, panel, trend, and cohort analysis}. Newbury Park: Sage
}
\references{
 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 Berlin: Springer

J. A. Hagenaars (1990). \emph{Categorical longitudinal data: log-linear, panel, trend, and cohort analysis}. Newbury Park: Sage
}

\examples{
data(DutchPolitics)

# Marginal homogeneity: A=C and B=D
at2a <- MarginalMatrix(c("A","B","C","D"), list(c("A"), c("C")), c(3, 3, 3, 3));
at2b <- MarginalMatrix(c("A","B","C","D"), list(c("B"), c("D")), c(3, 3, 3, 3));
bt2 <- ConstraintMatrix(c(1,2), list(c(1),c(2)), c(2,3));
at2 <- rbind(at2a, at2b);
bt2 <- DirectSum(bt2, bt2);

model <- list(bt2, "identity", at2);

mpolMH <- MarginalModelFit(DutchPolitics, model,
    MaxError = 10.^-25,
    MaxSteps = 200,
    MaxStepSize = .5,
    StartingPoint = "Automatic",
    CoefficientDimensions = c(2, 2, 3),
    ShowProgress = 50);

}

\keyword{datasets}
