%to do: more examples

\name{Antisemitism}
\alias{Antisemitism}
\docType{data}
\title{Change in antisemitism after seeing a movie}
\description{
A classical data set that has been used several times in the past, but not analyzed by means
of the methods advocated in this book (Glock, 1955; Campbell & Clayton, 1961; Hagenaars, 1990,
pp. 215-233, and Hagenaars, 1990, Section 5.3). The data are from a panel study among 503
white Christians living in and around Baltimore. The study's purpose was to determine the
effect of seeing the film `Gentleman's Agreement' on reducing the level of antisemitism
(Glock, 1955, p. 243). Antisemitism was measured in November 1947 (variable \eqn{A}{A}) prior to the
movie being locally shown and consisted of three categories : 1 = high, 2 = moderate, and
3 = low. Antisemitism was measured again in May 1948 (variable \eqn{B}{B}). In addition, the respondents
were asked whether or not they had (voluntary) seen the movie, which had been shown in Baltimore
theaters during the period between the two interviews (variable \eqn{X}{X}). The experimental group (with
\eqn{X=1}{X = 1}) consisted of those respondents who saw the movie; the control group (with \eqn{X=2}{X = 2})
consisted of those who did not. The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 5.8).

Section 5.2.2 in Bergsma, Croon, and Hagenaars (2009).
}

\usage{data(GSS93)}
\format{
  A data frame with 496 observations on the following three variables.
  \describe{
    \item{\code{X}}{Seen the film (factor):
        1 = Seen;
        2 = Not seen;
       }
    \item{\code{A}}{Antisemitism at Time 1 (ordered):
        1 = High;
        2 = Moderate;
        3 = Low.
       }
    \item{\code{B}}{Antisemitism at Time 2 (ordered):
        1 = High;
        2 = Moderate;
        3 = Low.
       }
  }
}

\source{
Glock (1955).

}
\references{
  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.

Campell & Clayton (1961)

Glock (1955)


Hagenaars, 1990
}

\examples{
data(Antisemitism)

## Sample marginal distributions
# at applied to data gives vectorized 2x2x3 table TXR (Time x Seen film or not x Response)
at <- MarginalMatrix(c("X","A","B"), list(c("X","A"), c("X","B")), c(2,3,3));
SampleStatistics(Antisemitism, at, Labels = c("T","X","R"), CoefficientDimensions = c(2,2,3));



## Models for table XR given T

# at1 applied to data gives vectorized conditional 2x3 table XR (XR conditional on T<-1)
at1 <- MarginalMatrix(c("X", "A", "B"), list(c("X", "A")), c(2, 3, 3));
# at2 applied to data gives vectorized conditional 2x3 table XR (XR conditional on T<-2)
at2 <- MarginalMatrix(c("X", "A", "B"), list(c("X", "B")), c(2, 3, 3));

bt1 <- ConstraintMatrix(c("X", "R"), list(c("X"), c("R")), c(2, 3));
bt2 <- ConstraintMatrix(c("X", "R"), list(c("X"), c("R")), c(2, 3));

model1 <- list(bt1, "log", at1);
model2 <- list(bt2, "log", at2);

# model1 doesn't converge, I don't know the reason and am trying to find out (it does converge in the Mathematica programme).
fit=MarginalModelFit(Antisemitism, model2, Labels = c("X","R"), CoefficientDimensions = c(2,3), MaxSteps=100, MaxStepSize=.5)




}
\keyword{datasets}
