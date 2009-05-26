\name{Smoking}
\alias{Smoking}
\docType{data}
\title{Smoking cessation after experimental intervention}
\description{
Data from an experiment designed for the investigation of the
effectiveness of a particular expert system intervention to convince
people to quit smoking. \eqn{N = 4,144}{N = 4,144} subjects
were randomly assigned to either the control (assessment only) or the
experimental condition (TTM intervention). Information was
collected on their smoking habits and their attitudes towards
smoking at the start of the study, at the sixth, twelfth, eighteenth, and twenty-fourth
month. For more detailed information see Bergsma et al. (2009) and Prochaska et al. (2001).

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Tables 5.11 to 5.14).

Section 5.2.3 in Bergsma, Croon and Hagenaars (2009).

}
\usage{data(Smoking)}
\format{
  A data frame with 4144 observations on the following variables.
  \describe{
    \item{\code{Group}}{(factor):
        1 = TTM intervention;
        2 = Assessment only.
       }
    \item{\code{smst00}}{Behavior at beginning (ordered):
        1 = Precontemplation;
        2 = Contemplation;
        3 = Preparation;
        4 = Action;
        5 = Maintenance.
       }
    \item{\code{smst06}}{Behavior after 6 months (ordered): see \code{smst00}}
    \item{\code{smst12}}{Behavior after 12 months (ordered): see \code{smst00}}
    \item{\code{smst18}}{Behavior after 18 months (ordered): see \code{smst00}}
    \item{\code{smst24}}{Behavior after 24 months (ordered): see \code{smst00}}
  }
}

\source{
Cancer Prevention Research Center, Univisity of Rhode Island, US.
 See Prochaska, Velicer, Fave, Rossi & Tosh (2001).
}
\references{

 Examples in book: \url{http://stats.lse.ac.uk/bergsma/cmm/R\%20files/Smoking.R}


 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

 Prochaska, J. O., Velicer, W. F., Fava, J. L. Rossi, J. S., & Tosh, J. Y. (2001).
 Evaluating a population-based recruitment approach and a stage-based expert system intervention for smoking cessation.
\emph{Addictive Behaviors, 26}, 583-602.

}

\examples{
####################################################################################
# Read data
data(Smoking)
dat <- Smoking

####################################################################################
# Table TXBR

# matrix producing 4x2x3x6 table TXBR
atTXBR = MarginalMatrix(c("X","B","R1","R2","R3","R4"), list(c("X","B","R1"), c("X","B","R2"), c("X","B","R3"), c("X","B","R4")), c(2, 3, 5, 5, 5, 5));
bt  = ConstraintMatrix(c("T","X","B","R"), list(c("T","X","B"), c("R")), c(4, 2, 3, 5))
model = list(bt,"log", atTXBR)

fit=MarginalModelFit(dat, model, MaxStepSize =.3, MaxSteps=100, ShowProgress=5)

}
\keyword{datasets}
