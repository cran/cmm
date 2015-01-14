\name{MarginalModelFit}
\alias{MarginalModelFit}

\title{MarginalModelFit}

\description{
 Fits marginal models, by default using maximum likelihood. 
}

\usage{
MarginalModelFit(dat, model, ShowSummary = TRUE, MaxSteps = 1000, MaxStepSize = 1, 
    MaxError = 1e-20, StartingPoint = "Automatic", MaxInnerSteps = 2, 
    ShowProgress = TRUE, CoefficientDimensions="Automatic", Labels="Automatic",
    ShowCoefficients = TRUE, ShowParameters = FALSE, ParameterCoding = "Effect",
    ShowCorrelations = FALSE, Method = "ML", Title = "Summary of model fit")
}

\arguments{
  \item{dat}{vector of frequencies or data frame}
  \item{model}{list specified eg as \code{list(bt,coeff,at)}}
  \item{ShowSummary}{Whether or not to execute \code{summary()} of the output}
  \item{MaxSteps}{integer: maximum number of steps of the algorithm}
  \item{MaxStepSize}{number greater than 0 and at most 1: step size}
  \item{MaxError}{numeric: maximum error term}
  \item{StartingPoint}{vector of starting frequencies corresponding to all cells in the manifest table}
  \item{MaxInnerSteps}{nonnegative integer: only used for latent variable models, indicates number of steps in M step of EM algorithms}
  \item{ShowProgress}{boolean or integer: FALSE for no progress information, TRUE or 1 for information at every step, an integer k for information at every k-th step}
  \item{CoefficientDimensions}{numeric vector of dimensions of the table in which the coefficient vector is to be arranged}
  \item{Labels}{list of characters or numbers indicating labels for dimensions of table in which the coefficient vector is to be arranged}
  \item{ShowCoefficients}{boolean, indicating whether or not the coefficients are to be displayed}
  \item{ShowParameters}{boolean, indicating whether or not the parameters (computed from the coefficients) are to be displayed}
  \item{ParameterCoding}{Coding to be used for parameters, choice of \code{"Effect"}, \code{"Dummy"} and  \code{"Polynomial"}}
  \item{ShowCorrelations}{boolean, indicating whether or not to show the correlation matrix for the estimated coefficients}
  \item{Method}{character, choice of "ML" for maximum likelihood or "GSK" for the GSK method}
  \item{Title}{title of computation to appear at top of screen output}
}

\details{
The data can be a data frame or vector of frequencies. \code{MarginalModelFit} converts a data frame \code{dat} to a vector of 
frequencies using \code{c(t(ftable(dat)))}.

The model specification is fairly flexible. We first describe the most typical way to specify the model. 
The model itself should typically first be written in the form of a constraint vector as
 \eqn{B'\theta(A'\pi) = 0}
where \emph{B'}  is a contrast matrix, \emph{A'} is matrix, normally of zeroes and ones, such that \emph{A'pi} gives a vector of marginal probabilities, and the function theta yields 
a list of (marginal) \emph{coefficients}. The model is then specified as \code{model=list(bt,coeff,at)} where \code{bt} is the matrix \emph{B'}, \code{at} is the matrix \emph{A'}, and \code{coeff}
represents the vector of coefficients using the generalized exp-log notation. For most of the models in the book, \code{bt} can be obtained directly using \code{ConstraintMatrix},  
 \code{coeff} can be obtained directly using \code{SpecifyCoefficient}, and \code{at} can be obtained directly using \code{MarginalMatrix}.

Note that CMM does not permit the \emph{C} and \emph{X} matrix in the model
 \eqn{C'\theta(A'\pi) = X\beta}
to be specified for use in the programme. The model has to be rewritten in terms of constraints as above, which is normally straightforward to do with the use of \code{ConstraintMatrix}. 
For many purposes, estimates and standard errors for a beta vector as in the equation above can still be obtained using the optional argument \code{ShowParameters=TRUE}.

There are two ways to specify \code{coeff}. The first is using the generalized exp-log notation, in which case \code{coeff[[1]]} should be a list of matrices, and 
\code{coeff[[2]]} should be a list of predefined functions of the same length. The second is to set \code{coeff} equal to a predefined function; for example, marginal loglinear models 
are obtained by setting \code{coeff="log"}.

The model can be specified in various other ways: as \code{model=list(coeff,at)}, \code{model=list(bt,coeff)}, \code{model=at}, or even just \code{model=coeff}.
Furthermore, the model
 \eqn{B'\theta(A'\pi) = d}
with \emph{d} a nonzero vector is specified in the form \code{model=list(bt,coeff,at,d)}.

To specify the simultaneous model
 \eqn{B'\theta(A'\pi) = 0\\ \log\pi=X\beta}
the extended model specification \code{model=list(margmodel,x)} should be used, where \code{margmodel} has one of the above forms, and \code{x} is a design matrix,
which can be obtained using \code{DesignMatrix}. Fitting is often more efficient by specifying a loglinear model for the joint distribution in this way rather than
using constraints.

The default on-screen output when running \code{fit=MarginalModelFit(...)} is given by \code{summary(fit)}. Important here is the distinction between coefficients and parameters, briefly 
described above. Standard output gives the coefficients. These are that part of \code{model} without the \code{bt} matrix, eg if the model is \code{list(bt,coeff,at)}
then the coefficients are \code{list(coeff,at)}. If other coefficients are needed, \code{\link{ModelStatistics}} can be used.

Latent variable models can be specified: if the size of the table for which \code{model} is specified is a multiple of the the size of the
observed frequencies specified in \code{dat}, it is assumed this is due to the presence of latent variables. With respect to vectorization,
the latent variables are assumed to change their value fastest.

Convergence may not always be achieved with \code{MaxStepSize=1} and a lower value may need to be used, but not too low or convergence is slow. If the step size is too large, 
a typical error message is "system is computationally singular: reciprocal condition number = 1.35775e-19"
}

\value{Most of the following are included in any output. Use \code{summary()} to get a summary of output.
 \item{FittedFrequencies}{Vector of fitted frequencies for the full table (including any latent variables).}
 \item{Method}{Fitting method used (currently maximum likelihood, GSK or minimum discrimination information)}
 \item{LoglikelihoodRatio}{}
 \item{ChiSquare}{}
 \item{DiscriminationInformation}{}
 \item{WaldStatistic}{}
 \item{DegreesOfFreedom}{}
 \item{PValue}{p-value based on asymptotic chi-square approximation for likelihood ratio test statistic}
 \item{SampleSize}{}
 \item{BIC}{}
 \item{Eigenvalues}{}
 \item{ManifestFittedFrequencies}{}
For the ``coefficients'' in the equation bt.coeff(at.pi)=d, the following statistics are available:
 \item{ObservedCoefficients}{}
 \item{FittedCoefficients}{}
 \item{CoefficientStandardErrors}{}
 \item{CoefficientZScores}{}
 \item{CoefficientAdjustedResiduals}{}
 \item{CoefficientCovarianceMatrix}{}
 \item{CoefficientCorrelationMatrix}{}
 \item{CoefficientAdjustedResidualCovarianceMatrix}{}
 \item{CoefficientDimensions}{}
 \item{CoefficientTableVariableLabels}{}
 \item{CoefficientTableCategoryLabels}{}
The ``parameters'' are certain linear combinations of the coefficients. For example, if the coefficients are log probabilities, then the parameters are the usual loglinear parameters. 
 \item{Parameters}{}
For the i-th subset of variables, the parameters are obtained by
 \item{Parameters[[i]]$}{}
The following statistics for the parameters belonging to each subset of variable are available.
 \item{Parameters[[i]]$ObservedCoefficients}{}
 \item{Parameters[[i]]$FittedCoefficients}{}
 \item{Parameters[[i]]$CoefficientStandardErrors}{}
 \item{Parameters[[i]]$CoefficientZScores}{}
 \item{Parameters[[i]]$CoefficientAdjustedResiduals}{}
 \item{Parameters[[i]]$CoefficientCovarianceMatrix}{}
 \item{Parameters[[i]]$CoefficientCorrelationMatrix}{}
 \item{Parameters[[i]]$CoefficientAdjustedResidualCovarianceMatrix}{}
 \item{Parameters[[i]]$CoefficientDimensions}{}
 \item{Parameters[[i]]$CoefficientTableVariableLabels}{}
 \item{Parameters[[i]]$CoefficientTableCategoryLabels}{}
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{SampleStatistics}}, \code{\link{ModelStatistics}}
}

\examples{
# see also the built-in data sets

data(NKPS)

# Fit the model asserting Goodman and Kruskal's gamma is zero for
# Child's attitude toward sex role's (NKPS[,3], three categories) and
# parent's attitude toward sex role's (NKPS[,4], three categories).

coeff = SpecifyCoefficient("GoodmanKruskalGamma",c(3,3))
fit = MarginalModelFit(NKPS[,c(3,4)], coeff )


# Marginal homogeneity (MH) in a 3x3 table AB
# Note that MH is equivalent to independence in the 2x3 table of marginals IR, in which 
# the row with I=1 gives the A marginal, and the row with I=2 gives the B marginal 
n <- c(1,2,3,4,5,6,7,8,9)
at <- MarginalMatrix(c("A","B"),list(c("A"),c("B")),c(3,3))
bt <- ConstraintMatrix(c("I","R"),list(c("I"),c("R")),c(2,3))
model <- list( bt, "log", at)
fit <- MarginalModelFit(n,model)

#Output can be tidied up:
fit <- MarginalModelFit(n,model,CoefficientDimensions=c(2,3))
}

\keyword{univar}
