%to do: examples

\name{MarihuanaAlcohol}
\alias{MarihuanaAlcohol}
\docType{data}
\title{Marihuana and alcohol use during adolescence, five-wave panel}
\description{
Panel study with five time points. A group of 269 youths were interviewed at ages 13, 14, 15, 16, and 17,
 and asked (among other things) about their marijuana and alcohol use (Eliot, Huizinga & Menard, 1989).
The data are tabulated in Bergsma, Croon, and Hagenaars (2009, p. 128).
208 observations do not have missing values.

Sections 4.2 and 4.4 in Bergsma, Croon, and Hagenaars (2009).
}
\usage{data(MarihuanaAlcohol)}
\format{
  A data frame with 269 observations on the following variables.
  \describe{
    \item{\code{Gender}}{(factor):
        1 = Male;
        2 = Female.
       }
    \item{\code{M1}}{Use of marihuana at time 1 (ordered):
        1 = Never;
        2 = Occasionally;
        3 = Frequently.
       }
    \item{\code{M2}}{Use of marihuana at time 2 (ordered): see \code{M1}}.
    \item{\code{M3}}{Use of marihuana at time 3 (ordered): see \code{M1}}.
    \item{\code{M4}}{Use of marihuana at time 4 (ordered): see \code{M1}}.
    \item{\code{M5}}{Use of marihuana at time 5 (ordered): see \code{M1}}.
    \item{\code{A1}}{Use of alcohol at time 1 (ordered): see \code{M1}}.
    \item{\code{A2}}{Use of alcohol at time 2 (ordered): see \code{M1}}.
    \item{\code{A3}}{Use of alcohol at time 3 (ordered): see \code{M1}}.
    \item{\code{A4}}{Use of alcohol at time 4 (ordered): see \code{M1}}.
    \item{\code{A5}}{Use of alcohol at time 5 (ordered): see \code{M1}}.
  }
}

\source{
US National Youth Survey (NYS): teenage marijuana and alcohol use (Elliot, Huizinga and Menard, 1989)
}
\references{

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

 Elliot, D. S., Huizinga, D. & Menard, S. (1989).
 Multiple problem youth: Delinquency, substance use, and metal health problems.
 New York: Springer.
}

\examples{
data(MarihuanaAlcohol)

# Table MA: marginal loglinear analysis  (BCH Section 4.2.1)
# listwise deletion of missing values and deletion of Gender and Alcohol use
dat <- MarihuanaAlcohol[-row(MarihuanaAlcohol)[is.na(MarihuanaAlcohol)],2:6]

# at yields the vectorized 5x3 table MA (marijuana use x age)
at <- MarginalMatrix(var =  c("M1", "M2", "M3", "M4", "M5"), 
 marg = list(c("M1"), c("M2"), c("M3"), c("M4"), c("M5")), 
 dim = c(3, 3, 3, 3, 3))
obscoeff <- SampleStatistics(dat = dat, 
 coeff = list("log", at), 
 CoefficientDimensions = c(5,3), 
 Labels = c("Age", "M"), 
 ShowCoefficients = FALSE, 
 ShowParameters = TRUE)
}
\keyword{datasets}
