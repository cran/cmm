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
}
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

 ## For Table 2.6, see SampleStatistics

 ## Reproduction of Table 2.7 in Bergsma, Croon, & Hagenaars (2009)
 Table.2.7.male   <- sapply(2:8,function(i){table(BodySatisfaction[BodySatisfaction[1]=="Male",i])})
 Table.2.7.male
 apply(Table.2.7.male,2,sum)                               #totals
 apply(Table.2.7.male,2,function(x){sum(c(1:5)*x/sum(x))}) #means
 sqrt(apply(Table.2.7.male,2,function(x){(sum(c(1:5)^2*x/sum(x)))-(sum(c(1:5)*x/sum(x)))^2}))#standard deviations


 ## Fit marginal homogeneity model
 # matrix producing 1-way marginals, ie the 7x5 table IS
 at75 <- MarginalMatrix( c(1, 2, 3, 4, 5, 6, 7), list(c(1),c(2),c(3),c(4),c(5),c(6),c(7)), c(5, 5, 5, 5, 5, 5, 5) )
 # model specifying independence of I and S, i.e., marginal homogeneity
 bt    <- ConstraintMatrix( c("I","S"), list(c("I"),c("S")), c(7,5) )
 model <- list(bt, "log", at75 )        # define model
 dat   <- BodySatisfaction[,2:8]        # omit first column corresponding to gender
#AA# fit   <- MarginalModelFit(dat, model, CoefficientDimensions=c(7,5),Labels=c("I","S"))# fit the model


 ## Fit marginal homogeneity model for means
 # matrix producing 1-way marginals, ie the 7x5 table IS
 at75 <- MarginalMatrix( c(1, 2, 3, 4, 5, 6, 7), list(c(1),c(2),c(3),c(4),c(5),c(6),c(7)), c(5, 5, 5, 5, 5, 5, 5) )
 # specification for means in a 5x1 table, repeated 7 times for the 7 items
 meanspec7 <- SpecifyCoefficient("Mean", c(1, 2, 3, 4, 5), 7 )
 # model specifying equality of means in the 7 one-way marginal tables
 bt    <- ConstraintMatrix( c(1), c(), c(7) )
 model <- list(bt, meanspec7, at75 )        # define model
 dat   <- BodySatisfaction[,2:8]            # omit first column corresponding to gender
#AA# fit   <- MarginalModelFit(dat, model)      # fit the model




####################################################################################
# Models for marginal means, variances, etc
# Table IS (also subgroups: men, women)

# matrix producing 1-way marginals, ie the 7x5 table IS
at75 = MarginalMatrix( c(1, 2, 3, 4, 5, 6, 7), list(c(1),c(2),c(3),c(4),c(5),c(6),c(7)), c(5,5,5,5,5,5,5) )

# select one of the coefficients and associated parameter
coefficientname <- "Mean"; param = c(1,2,3,4,5);
#coefficientname <- "Variance"; param = c(1,2,3,4,5)
#coefficientname <- "StandardDeviation"; param = c(1,2,3,4,5)
#coefficientname <- "GiniMeanDifference"; param = c(1,2,3,4,5)
#coefficientname <- "Entropy"; param = 5
#coefficientname <- "DiversityIndex"; param = 5

# specification for coefficients in a 5x1 table, for 7 items
spec7 = SpecifyCoefficient( coefficientname, param, 7 )

# model specifying equality of coefficients in the 7 one-way marginal tables
bt1 <- ConstraintMatrix( c(1), c(), c(7) )
model1 <- list( bt1, spec7, at75 )

dat7all   <- BodySatisfaction[,2:8]                 # omit first column corresponding to gender
dat7men   <- BodySatisfaction[BodySatisfaction=="Male",][2:8] # select men (first column a zero)
dat7women <- BodySatisfaction[BodySatisfaction=="Female",][2:8] # select women (first column a one)

# fit the models
#AA#pi11 <- MarginalModelFit(dat7all, model1,MaxSteps=10)    # 7 equal coefficients men+women table IS
#AA#pi12 <- MarginalModelFit(dat7men, model1,MaxSteps=10)    # 7 equal coefficients men table IS
#AA#pi13 <- MarginalModelFit(dat7women, model1,MaxSteps=10)  # 7 equal coefficients women table IS



####################################################################################
# Models for marginal means, variances, etc
# Table IGS
# NB: THE FOLLOWING ANALYSES ARE COMPUTATIONALLY INTENSIVE AND FOR THIS REASON COULD NOT GET THROUGH
# THE R-CHECK, SO PLEASE REMOVE THE #'S WHERE APPROPRIATE BEFORE RUNNING (IN PARTICULAR: BEFORE at725, AND EG model2 AND pi14

# matrix producing 2-way marginals, ie the 7x2x5 table IGS
#at725 = MarginalMatrix( c(1, 2, 3, 4, 5, 6, 7, 8), list( c(1,2), c(1,3), c(1,4), c(1,5), c(1,6), c(1,7), c(1,8) ), c(2, 5, 5, 5, 5, 5, 5, 5) )

# select one of the coefficients and associated parameter
coefficientname <- "Mean"; param = c(1,2,3,4,5);
#coefficientname <- "Variance"; param = c(1,2,3,4,5)
#coefficientname <- "StandardDeviation"; param = c(1,2,3,4,5)
#coefficientname <- "GiniMeanDifference"; param = c(1,2,3,4,5)
#coefficientname <- "Entropy"; param = 5
#coefficientname <- "DiversityIndex"; param = 5

# specification for coefficients in a 5x1 table, for 7x2 table IG
spec14 = SpecifyCoefficient( coefficientname, param, 14 )

# Model of equality of all 14 coefficients in the 7x2x5 table IGS
bt2 = ConstraintMatrix( c(1,2), c(2), c(7,2) )
#model2 = list( bt2, spec14, at725 )

# no 3-variable interaction for coefficients in the 7x2x5 table IGS
bt3 = ConstraintMatrix( c(1,2), list( c(1), c(2) ), c(7,2) )
#model3 = list( bt3, spec14, at725 )

#pi14 <- MarginalModelFit(BodySatisfaction, model2,MaxSteps=50)    # 14 equal coefficients men+women table IGS
#pi15 <- MarginalModelFit(BodySatisfaction, model3,MaxSteps=10)    # no 3-variable interaction for coefficients in 7x2x5 table IGS

}
\keyword{datasets}
