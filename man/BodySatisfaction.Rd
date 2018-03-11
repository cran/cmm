\name{BodySatisfaction}
\alias{BodySatisfaction}
\docType{data}
\title{Body satisfaction for seven body parts}
\description{
A group of 301 university students (204 women and 97 men) answered questions about their degrees of
satisfaction with different parts or aspects of their body by completing the Body Esteem Scale
(Franzoi & Shields, 1984; Bekker, Croon, & Vermaas, 2002). This scale consisted of 22 items (not counting
the items concerning gender-specific body parts), seven of which will be considered here.
These seven items loaded highest on the first unrotated principal component, with loadings higher than .70.
Principal component analysis was used to discover whether the separate expressions of satisfaction with
the different body aspects can be seen as just an expression of the general underlying satisfaction with
the body as a whole or whether more underlying dimensions are needed
(for the interested reader: two rotated factors were needed to explain the correlations among
 all the 22 items, one having to do with the general appearance of the body and the other with the
 satisfaction with the parts of one's face; the items chosen here all belong to the first factor.)
The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 2.5, Table 2.7).

See Sections 2.2.2 and 3.1 of Bergsma, Croon, and Hagenaars (2009).

Several worked examples involving this data set are listed below but more can be found at http://stats.lse.ac.uk/bergsma/cmm/R files/BodySatisfaction.R}

\usage{data(BodySatisfaction)}
\format{
  A data frame with 301 observations on the following variables.
  \describe{
    \item{\code{Gender}}{(factor):
        0 = Male;
        1 = Female.
       }
    \item{\code{Thighs}}{(ordered):
        1 = Very dissatisfied;
        2 = Moderately dissatisfied;
        3 = Slightly satisfied.
        4 = Moderately satisfied.
        5 = Very satisfied.
       }
    \item{\code{BodyBuild}}{(ordered): see \code{Thighs}}
    \item{\code{Buttocks}}{(ordered): see \code{Thighs}}
    \item{\code{Hips}}{(ordered): see \code{Thighs}}
    \item{\code{Legs}}{(ordered): see \code{Thighs}}
    \item{\code{Figure}}{(ordered): see \code{Thighs}}
    \item{\code{Weight}}{(ordered): see \code{Thighs}}
  }
}

\source{
 Bekker, Croon, & Vermaas (2002).
}
\references{

 Bekker, M.H.J., Croon, M.A., & Vermaas, S. (2002).
 Inner body and outward appearance- the relationship between orientation toward outward appearance, body awareness and symptom perception.
 \emph{Personality and Individual Differences, 33}, 213-225.

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

 Franzoi, S.L. & Shields, S.A. (1984).
 The Body-Esteem Scale: Multidimensional structure and sex differences in a college population.
 \emph{Journal of Personality Assessment, 48}, 173-178.
}

\examples{
data(BodySatisfaction)

## Reproduction of Table 2.5 in Bergsma, Croon, & Hagenaars (2009)
sapply(2:8,function(i){table(BodySatisfaction[,i])})

## Table 2.6 in Bergsma, Croon and Hagenaars (2009). 
## Loglinear parameters for marginal table IS
## We provide two to obtain the parameters

## Reproduction of Table 2.7 in Bergsma, Croon, & Hagenaars (2009)
Table.2.7.male <- 
 sapply(2:8,function(i){table(BodySatisfaction[BodySatisfaction[1]=="Male",i])})
Table.2.7.male
#totals
apply(Table.2.7.male,2,sum)                               
#means
apply(Table.2.7.male,2,function(x){sum(c(1:5)*x/sum(x))}) 
#standard deviations
sqrt(apply(Table.2.7.male,2,function(x){(sum(c(1:5)^2*x/sum(x)))-(sum(c(1:5)*x/sum(x)))^2}))
                                                           

\dontrun{
dat   <- BodySatisfaction[,2:8]        # omit first column corresponding to gender

# matrix producing 1-way marginals, ie the 7x5 table IS
at75 <- MarginalMatrix(var = c(1, 2, 3, 4, 5, 6, 7), 
  marg = list(c(1),c(2),c(3),c(4),c(5),c(6),c(7)), 
  dim = c(5, 5, 5, 5, 5, 5, 5))
# First method: the "coefficients" are the log-probabilities, 
# from which all the (loglinear) parameters are calculated
stats <- SampleStatistics(dat = dat, 
  coeff = list("log", at75), 
  CoefficientDimensions=c(7, 5),
  Labels=c("I", "S"),
  ShowCoefficients = FALSE,
  ShowParameters = TRUE)

 # Second method: the "coefficients" are explicitly specified as being the 
 # (highest-order) loglinear parameters
 loglinpar75 <- SpecifyCoefficient("LoglinearParameters", c(7,5) )
 stats = SampleStatistics(dat = dat, 
  coeff = list(loglinpar75, at75), 
  CoefficientDimensions = c(7, 5), 
  Labels = c("I", "S"))
}
#For further worked examples from the book, 
# see http://stats.lse.ac.uk/bergsma/cmm/R files/BodySatisfaction.R
}
\keyword{datasets}
