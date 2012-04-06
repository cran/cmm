\name{ClarenceThomas}
\alias{ClarenceThomas}
\docType{data}
\title{Opinion on Supreme Court nominee Clarence Thomas, two-wave panel study}
\description{
Clarence Thomas was nominated in 1991 as member of the U.S. Supreme Court by President George H. W. Bush.
The nomination provoked some public debate because of Clarence Thomas' race (black) and because of his
allegedly extremely conservative social and political views. A panel of U.S.citizens was interviewed
regarding their opinion on Clarence Thomas' candidacy during September 3-5 (A) and on October 9 (B).
After the first wave, more precisely on September 25, a charge of sexual harassment was brought against
Clarence Thomas by his former aide, Anita Hill. Source: CBS News and New York Times 2001.

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 5.6) and were also used in
Bergsma & Croon (2005).

Section 5.2.1 in Bergsma, Croon, and Hagenaars (2009).

}
\usage{data(ClarenceThomas)}
\format{
  A data frame with 991 observations on the following variables.
  \describe{
    \item{\code{A}}{Opinion on Clarence Thomas during first wave, Sept 3-5, 1991  (factor):
        1 = Favorable;
        2 = Unfavorable;
        3 = Undecided;
        4 = Haven't heard enough;
       }
    \item{\code{B}}{Opinion on Clarence Thomas during second wave, Oct 9, 1991  (factor):
        1 = Favorable;
        2 = Unfavorable;
        3 = Undecided;
        4 = Haven't heard enough;
       }
  }
}

\source{
CBS News and New York Times 2001.
}
\references{
 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 Berlin: Springer

 Bergsma, W. P., & Croon, M. A. (2005).
 Analyzing categorical data by marginal models.
 In L. A. van der Ark, M. A. Croon, & K. Sijtsma (Eds.),
 \emph{New developments in categorical data analysis for the social and behavioral sciences.}
 Mahwah, NJ: Erlbaum.

}

\examples{
data(ClarenceThomas)

################################################################
## Marginal homogeneity: O1=O2

# at24 produces vectorized 2x4 table TR (Time x Response)
at24 <- MarginalMatrix(c("A", "B"), list(c("A"), c("B")), c(4, 4));

# marginal homogeneity
bt1 <- ConstraintMatrix(c("T", "R"), list(c("T"), c("R")), c(2, 4));
model1 <- list(bt1, "log", at24);

# only first two categories are equated
bt2 <- rbind(
   c(1, 0, 0, 0,  -1, 0, 0, 0),
   c(0, 1, 0, 0,   0,-1, 0, 0));
model2 <- c(bt2, "log", at24);

pi11 <- MarginalModelFit(ClarenceThomas, model1,
    MaxSteps = 500,
    ShowProgress = 20,
    MaxStepSize = .5,
    CoefficientDimensions = c(2, 4),
    Labels = c("T", "R"),
    Title = "Clarence Thomas data, MH");


################################################################
## Marginal homogeneity: P1=P2
# P1 and P2 are O1 and O2 conditioned on not being in category 4

# at24 produces vectorized 2x4 table TR (Time x Response
at24 <- MarginalMatrix(c("A", "B"), list(c("A"), c("B")), c(4, 4));

# specify conditional probabilities using generalized exp-log notation
at1 <- rbind(c(1, 0, 0, 0), c(0, 1, 0, 0), c(0, 0, 1, 0), c(1, 1, 1, 0));
at1 <- DirectSum(at1, at1);
at2 <- rbind(c(1, 0, 0, -1), c(0, 1, 0, -1), c(0, 0, 1, -1));
at2 <- DirectSum(at2, at2);
coeff <- list(list(diag(6), at2, at1), list("exp", "log", "identity"));

# marginal homogeneity
bt1 <- ConstraintMatrix(c("T", "R"), list(c("T"), c("R")), c(2, 3));

model1 <- list(bt1, coeff, at24);

pi11 <- MarginalModelFit(ClarenceThomas, model1,
    MaxSteps = 500,
    ShowProgress = 20,
    MaxStepSize = .5,
    CoefficientDimensions = c(2, 3),
    Labels = c("T", "R"),
    Title = "Clarence Thomas data, MH");

}
\keyword{datasets}
