\name{MarginalModelFit}
\alias{MarginalModelFit}

\title{MarginalModelFit}

\description{
 Fits marginal model
}

\usage{
MarginalModelFit(dat, model, MaxSteps=1000, MaxStepSize=1, MaxError=1e-20, StartingPoint="Automatic",
    MaxInnerSteps=2, ShowProgress=TRUE, CoefficientDimensions="Automatic",
    Labels="Automatic",ShowCoefficients=TRUE,ShowParameters=FALSE, ParameterCoding="Effect",
    ShowCorrelations=FALSE, Method="ML", Title="" )
}

\arguments{
  \item{dat}{vector of frequencies or data frame}
  \item{model}{list specified eg as \code{list(bt,coeff,at)}}
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
The data can be a data frame or vector of frequencies. \code{MarginalModelFit} converts a data frame \code{dat} using \code{c(t(ftable(dat)))}.

The model can be specified in various ways, eg, as \code{list(bt,coeff,at)} where \code{bt} may be obtained using \code{ConstraintMatrix},
\code{coeff} using \code{SpecifyCoefficient} and \code{at} using \code{MarginalMatrix}. Alternatively, \code{list(coeff,at)} or \code{list(coeff,at)}
can be used. Furthermore, \code{coeff} can be a function, eg, a loglinear marginal model can be specified using \code{list(bt,"log",at)}.

An extended model specification is \code{list(margmodel,x)} where \code{margmodel} has one of the above forms, and \code{x} is a design matrix,
which can be obtained using \code{DesignMatrix}. In addition to the marginal model \code{margmodel}, this specifies a loglinear model based
on design matrix \code{x}. Fitting is often more efficient by specifying a loglinear model for the joint distribution in this way rather than
using constraints.

In the output, coefficients are given. These are that part of \code{model} without the \code{bt} matrix, eg if the model is \code{list(bt,coeff,at)}
then the coefficients are \code{list(coeff,at)}. If other coefficients are needed, \code{\link{ModelStatistics}} can be used.

Latent variable models can be specified: if the size of the table for which \code{model} is specified is a multiple of the the size of the
observed frequencies specified in \code{dat}, it is assumed this is due to the presence of latent variables. With respect to vectorization,
the latent variables are assumed to change their value fastest, ie, their values change fastest.

Convergence may not be achieved with \code{MaxStepSize=1} and a lower value may need to be used, not too low or convergence is slow.
}

\value{
 NA. Only output to the screen is provided
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

# Compute Goodman and Kruskal's gamma for
# Child's attitude toward sex role's (NKPS[,3], three categories) and
# parent's attitude toward sex role's (NKPS[,4], three categories).

coeff = SpecifyCoefficient("GoodmanKruskalGamma",c(3,3))
MarginalModelFit(NKPS[,c(3,4)], coeff )

}

\keyword{univar}
