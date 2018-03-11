\name{TestCronbachAlpha}
\alias{TestCronbachAlpha}
\docType{data}
\title{Testing Cronbach's alpha using marginal models}

\description{
Data set \code{TestCronbachAlpha} is a simulated data set that is used to demonstrate 
 the statistical testing of three relevant hypotheses involving Cronbach's alpha:
 H01: alpha equals a particular criterion;
 H02: testing the equality of two alpha coefficients for independent samples; and
 H03: testing the equality of two alpha coefficients for dependent samples.

 This R document file may be regarded as an appendix to Kuijpers, Van der Ark, and Croon (2012) who discussed this topic.
 Hence, all references to equations pertain to this paper.
 The \emph{Details} section describes the required objects for testing the three hypotheses.
 The \emph{Examples} section describes the actual code required for for testing the three hypotheses.
}

\usage{data(TestCronbachAlpha)}

\format{
 A 400 by 21 matrix, representing the dichotomous item scores of 400 respondents from two groups for two tests.
 The first column is the grouping variable: Group \code{1} and Group \code{2} each consist of 200 observations. 
 Columns 2-11 are the items score of Test 1. Columns 12-21 are the item scores of Test 2. So each test includes 
 \emph{J} = 10 items having \emph{K} = 2 item scores.
 Note that in Kuijpers et al. (2012), \emph{k} is used rather than \emph{K}; \emph{k} = \emph{K} - 1.
 Data files
 \verb{TestCronbachAlphaH1 <- TestCronbachAlpha[1:200,2:11]}
 \verb{TestCronbachAlphaH2 <- TestCronbachAlpha[1:400,1:11]}
 and
 \verb{TestCronbachAlphaH3 <- TestCronbachAlpha[1:200,2:21]}
 will be used to test hypotheses H01, H02, and H03, respectively.
}

\details{
  Vector \bold{m} is estimated under the general categorical marginal model \bold{g}(\bold{m}) = \bold{d}.
  Objects \code{coeff}, \code{bt}, and \code{at} define function \bold{g}(\bold{m}).

\tabular{ll}{
 \code{coeff} \tab Includes the design matrices and functions (i.e., exp and log) of the coefficients  of interest. \cr      
              \tab Function \link{SpecifyCoefficient} returns the design matrices and functions of several prespecified coefficients, including Cronbach's alpha. \cr
              \tab The argument \code{arg} in \link{SpecifyCoefficient} specifies for which of the \emph{J} marginals Cronbach's alpha should be computed, and it specifies the number of response categories \emph{K}. \cr
              \tab Furthermore, the argument \code{data} in \link{SpecifyCoefficient} specifies for which data set Cronbach's alpha should be computed (for example for data set \code{mydata}). \cr
              \tab                                                                                                        \cr
              \tab For hypothesis H01, which involves only one Cronbach's alpha, \code{coeff} is obtained by              \cr
              \tab  \verb{coeff = SpecifyCoefficient(name = "CronbachAlpha", arg = list(list(1 : J), K), data = mydata)}  \cr
              \tab For H01, object \code{coeff} includes the design matrices and functions in Equation 10.                \cr
              \tab                                                                                                        \cr
              \tab For hypothesis H02, which involves two alpha coefficients derived from two independent samples, \code{coeff} is obtained by \cr
              \tab \verb{coeff = SpecifyCoefficient(name = "CronbachAlpha", arg = list(list(2 : (J + 1), 2 : (J + 1)), c(K, K), 1), data = mydata, )} \cr
              \tab For H02, \code{coeff} now includes the design matrices and functions in Equation 19. \cr
              \tab                                                                                                        \cr
              \tab For hypothesis H03, which involves two dependent alpha coefficients, \code{coeff} is obtained by       \cr
              \tab \verb{coeff = SpecifyCoefficient(name="CronbachAlpha", arg=list(list(test1, test2),c(K,K)), data=mydata,)}\cr
              \tab For H03, object \code{coeff} includes the design matrices and functions in Equation 23. \cr
              \tab                                                                                                        \cr
 \code{bt}    \tab Is called the \emph{constraint matrix} and relates the  coefficients defined in \code{coeff}. Hypothesis H01 pertains to one Cronbach's alpha, so \code{bt} is the scalar 1. For hypotheses H02 and H03 \code{bt} equals design matrix A6. \cr
              \tab                                                                                                        \cr
\code{at}     \tab Is called the \emph{marginal matrix}. The marginal matrix was not specified for hypotheses H01 and H02, which is equivalent to including the identity matrix as the marginal matrix in Equations 10 (H01) and 18 (H02). Hence \code{at} = \bold{I}.\cr
              \tab For hypotheses H03 the marginal matrix is equal to design matrix \bold{A}_0 (p. 16). Function \link{MarginalMatrix} constructs the marginal matrix. \cr
\code{d}      \tab Vector \bold{d} in Equation 9.\cr               
}

Function  \link{MarginalModelFit} estimates the categorical marginal model (CMM), and requires the following arguments: the vector of observed frequencies, \code{n}, and model 
specifications in \code{coeff}, \code{bt}, \code{at}, and \code{d}.

In the example for testing hypothesis H01, data set \code{TestCronbachAlphaH1} was used, which contained the 200 item-score vectors from the first group,
 for the first test. For this data set, Cronbach's alpha is equal to 0.793. If a researcher wants to test whether this value is 
 significantly above .75, the software code for the first example in the paragraph
 \code{Examples} can be used (see below). First, the R package \code{cmm} needs to be invoked. Second, vector \bold{n},
 the number of items \emph{J}, the number of categories \emph{K}, and criterion \emph{c} in hypothesis H01 have to be defined. 
 The fit of this marginal model
 is evaluated by \emph{G}^2, with \emph{D} = 1 degree of freedom. In general, \emph{G}^2 pertains to a two-sided test. However, here H01 is a one-sided hypothesis,
 the value of \emph{G}^2 at the 2 alpha level is used. For alpha = 0.05, H01 must be rejected if \emph{G}^2 > 2.71 (i.e., \emph{p} = .10) and r_{alpha} > c.
 The results of the analysis show that \emph{G}^2 = 3.301 with \emph{p} = 0.069, so for this example we can conclude that the alpha of this data set (i.e.,
 r_{alpha} = 0.793) is significantly above .75.

For testing hypothesis H02, data set \code{TestCronbachAlphaH2} was used, which contained the item-score vectors from the two independent groups for the first 
 test, and an additional variable indicating group membership.
 For this data set, Cronbach's alpha for the first independent group is equal to 0.793, for the second independent group alpha is equal to 0.737. To test
 whether the alphas of the two independent groups are equal, the software code for the second example in the paragraph \emph{Examples} can be used (see below).
 Note that the first item indicates group membership. Hence, for \emph{J} items, vector \bold{n} is based on \emph{J}+1 patterns. \emph{G}^2 is used to assess the 
 fit of this marginal model with \emph{D} = 1 degree of freedom, so H02 must be rejected if \emph{G}^2 > 3.84 (i.e., alpha = .05).
 The results of the analysis show that \emph{G}^2 = 2.774 with \emph{p} = 0.096, so for this example we can conclude that the alphas of the two independent samples
 (i.e., r_{alpha_{g1}} = 0.793 and r_{alpha_{g1}} = 0.737) are equal.

For hypothesis H03, data set \code{TestCronbachAlphaH3} was used, which contained the 200 item-score vectors from the first group for the two tests. 
 The data of each test forms one dependent group. For this data set,
 Cronbach's alpha for the first dependent group is equal to 0.793, for the second dependent group alpha is equal to 0.696. For H03, the marginal matrix
 is not implemented in the package as a code yet, so it has to be computed ad hoc. To test whether the alphas of the two dependent groups are equal, the
 software code for the third example in the paragraph \emph{Examples} can be used (see below). \emph{G}^2 is used to assess the fit of this marginal model
 with \emph{D} = 1 degree of freedom. The results of the analysis show that \emph{G}^2 = 9.898 with \emph{p} = 0.002. Using alpha = .05, we can conclude 
 that the alphas of the two dependent samples (i.e., r_{alpha_{t1}} = 0.793 and r_{alpha_{t1}} = 0.696) are not equal to each other.
}

\references{

Kuijpers, R. E., Van der Ark, L. A., & Croon, M. A. (2012).
Testing hypotheses involving Cronbach's alpha using marginal models.
Manuscript submitted for publication.

}

\author{Renske E. Kuijpers, L. Andries van der Ark}

\seealso{
\code{\link{cmm}, \link{SpecifyCoefficient}, \link{MarginalMatrix}},
}

\examples{
data(TestCronbachAlpha)

#Example 1: Testing H01.
  
  # Invoke cmm
  library(cmm)

  # Data
  TestCronbachAlphaH1 <- TestCronbachAlpha[1 : 200, 2 : 11]
  
  # Transform data into vector of frequencies n
  n <- as.matrix(table(apply(TestCronbachAlphaH1, 1, paste, collapse = "")))

  # Specify number of items
  J <- 10 
  
  # Specify number of item scores
  K <- 2 
  
  # Specify criterion for Hypothesis H01
  criterion <- .75

  # Compute object coeff
  coeff <- SpecifyCoefficient(name = "CronbachAlpha", arg = list(list(1 : J), K),
    data = TestCronbachAlphaH1)

  # Compute object at (marginal matrix)
  L <- ncol(coeff[[1]][[5]])
  at <- diag(L)

  # Compute object bt (constraint matrix)
  bt <- matrix(1)
  
  # Compute object d
  d <- criterion

  # Compute CMM
  model <- list(bt, coeff, at, d)
  fit <- MarginalModelFit(n, model, MaxError = 1e-04)

#Example 2: Testing H02.
\donttest{          
  # Data
  TestCronbachAlphaH2 <- TestCronbachAlpha[1 : 400, 1 : 11]
  
  # Transform data into vector of frequencies n
  n <- as.matrix(table(apply(TestCronbachAlphaH2, 1, paste, collapse = "")))

  # Specify number of items
  J <- 10

  # Specify number of item scores
  K <- 2
  
  # Compute object coeff
  coeff <- SpecifyCoefficient(name = "CronbachAlpha", arg = list(list(2 : (J + 1),
    2 : (J + 1)), c(K, K), 1), data = TestCronbachAlphaH2,)

  # Compute object at (marginal matrix)
  L <- ncol(coeff[[1]][[5]])
  at <- diag(L)

  # Compute object bt (constraint matrix)
  bt <- matrix(c(1,-1),1,2)

  # Compute object d
  d <- rep(0,nrow(bt))

  # Compute CMM
  model <- list(bt,coeff,at,d)
  fit <- MarginalModelFit(n, model, MaxError = 1e-04)
}  
#Example 3: Testing H03.
\donttest{          
  # Data
  TestCronbachAlphaH3 <- TestCronbachAlpha[1 : 200, 2 : 21]

  # Transform data into vector of frequencies n
  n <- as.matrix(table(apply(TestCronbachAlphaH3, 1, paste, collapse = "")))

  # Specify number of items
  J <- 20

  # Specify number of item scores
  K <- 2
  
  # Specify which items belong to which test
  test1 <-  1 : 10
  test2 <- 11 : 20
  
  # Compute object coeff
  coeff <- SpecifyCoefficient(name = "CronbachAlpha", arg = list(list(test1,
     test2), c(K, K)), data = TestCronbachAlphaH3,)

  # Compute object at (marginal matrix)
  x <- dimnames(n)[[1]]
  p1 <- sort(unique(substr(x, test1[1] ,test1[length(test1)])))
  p2 <- sort(unique(substr(x, test2[1] ,test2[length(test2)])))
  U1 <- matrix(NA, length(p1), length(x))
  for (h1 in 1 : length(p1))
  U1[h1, ] <- as.numeric(substr(x, test1[1], test1[length(test1)]) == p1[h1])
  U2 <- matrix(NA, length(p2), length(x))
  for (h2 in 1 : length(p2))
  U2[h2, ] <- as.numeric(substr(x, test2[1], test2[length(test2)]) == p2[h2])
  at <- rbind(U1, U2)

  # Compute object bt (constraint matrix)
  bt <- matrix(c(1, -1), 1, 2)

  # Compute object d
  d <- rep(0, nrow(bt))

  # Compute CMM
  model <- list(bt, coeff, at, d)
  fit <- MarginalModelFit(n, model, MaxError = 1e-04)
}
}


\keyword{datasets}
