%to do: fit loglinear model for table SCT (write proc for fitting ll models)

\name{DutchConcern}
\alias{DutchConcern}
\docType{data}
\title{Concern about crime and social security in the Netherlands}
\description{
Data from a trend study where two survey questions, regarding (i) concern about crime and
(ii) concern about social security, were asked to randomly selected people in the Netherlands at
ten different time points (November 1977 to July 1981).
The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 4.1, Table 4.2).

Section 4.1 in Bergsma, Croon, and Hagenaars (2009).
}
\usage{data(DutchConcern)}
\format{
  A data frame with 5742 observations on the following variables.
  \describe{
    \item{\code{S}}{Concern about social security (ordered):
        1 = No (big) problem;
        2 = big problem;
        3 = Very big problem.
       }
    \item{\code{C}}{Concern about crime (ordered):
        1 = No (big) problem;
        2 = big problem;
        3 = Very big problem.
       }
    \item{\code{T}}{time points (factor):
        1 = Nov 1977;
        2 = Jan 1978;
        3 = Jun 1978;
        4 = Nov 1978;
        5 = Mar 1979;
        6 = Oct 1979;
        7 = Apr 1980;
        8 = Oct 1980;
        9 = Dec 1980;
       10 = Jan 1981.
       }
  }
}

\source{
 Hagenaars (1990, p. 289) and Continuous survey, University of Amsterdam / Steinmetz Archives Amsterdam.

}
\references{
 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 Berlin: Springer

 Hagenaars, J. A. P. (1990).
 \emph{Categorical longitudinal data: Log-linear panel, trend, and cohort analysis}.
 Newbury Park, CA: Sage.
}

\examples{
data(DutchConcern)
n=c(t(ftable(DutchConcern)))

# Table 4.2
#NB: PLEASE REMOVE THE "#" BEFORE APPLY IN NEXT LINES, WON'T GO THROUGH R-CHECK OTHERWISE/
at1 = MarginalMatrix(c("S", "C", "T"), c("S", "T"), c(3, 3, 10));
print("Concern about social security:")
#apply(matrix(at1 %*% n, 10),1,function(x){100*x/sum(x)})
at2 = MarginalMatrix(c("S", "C", "T"), c("C", "T"), c(3, 3, 10));
print("Concern about crime:")
#apply(matrix(at2 %*% n, 10),1,function(x){100*x/sum(x)})


##############################################################################
# Define and fit models for marginal table IRT (Section 4.1.1)

# atIRT %*% n produces IRT table, dimension 2x3x10
atIRT = MarginalMatrix(c("S", "C", "T"), list(c("S", "T"), c("C", "T")), c(3, 3, 10));
# bt1.Log(atIRT.pi)=0 is marginal model for independence of IT and R \
bt1 = ConstraintMatrix(c("I", "R", "T"), list(c("I", "T"), c("R")), c(2, 3, 10));
bt2 = ConstraintMatrix(c("I", "R", "T"), list(c("I", "T"), c("R", "T")), c(2, 3, 10));
bt3 = ConstraintMatrix(c("I", "R", "T"), list(c("I", "T"), c("I", "R")), c(2, 3, 10));
bt4 = ConstraintMatrix(c("I", "R", "T"), list(c("I", "T"), c("I", "R"), c("R", "T")), c(2, 3, 10));

model1 = list(bt1, "log", atIRT);
model2 = list(bt2, "log", atIRT);
model3 = list(bt3, "log", atIRT);
model4 = list(bt4, "log", atIRT);

#  change model1 to model2 etc to fit different models
pi1 = MarginalModelFit(n, model4,
   ShowProgress = 5,
   CoefficientDimensions = c(2, 3, 10),
   Labels = c("I", "R", "T"));

##############################################################################
# Simultaneous model for marginal and joint distributions (Section 4.1.2)

# define x, the design matrix for the loglinear model of Eq. 4.1
x = DesignMatrix(c("S","C","T"), c("S","C","T"), c(3,3,10), SubsetCoding = list(c("S", "C", "T"),list("Nominal","Nominal","Linear")));
# model6 is the simultaneous model
model6 = list(model4, x);

# NB: when fitting model6 Labels and CoefficientDimensions should be appropriate to get the right output
# for table IRT, which is different than for model5
#NB: REMOVE "#" IN NEXT LINE, WON'T GO THROUGH R-CHECK
#pi5 = MarginalModelFit(DutchConcern, model6, ShowProgress = 5, CoefficientDimensions = c(2, 3, 10), Labels = c("I", "R", "T"), MaxSteps = 500, MaxStepSize=.2);


}
\keyword{datasets}
