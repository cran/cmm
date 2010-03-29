\name{JoinModels}
\alias{JoinModels}
\title{JoinModels}

\description{Returns the simultaneous specification of two models}

\usage{JoinModels(...)}

\arguments{
\item{...}{list of `compatible' models, i.e., each model is specified using the same number of functions (and matrices)}
}

\details{
Models can be of any form allowed in CMM (see \code{MarginalModelFit}), eg, \code{list(bt,coeff,at)}, with the restriction that the number of columns of the
\code{at} matrices must be equal, and the list of functions in \code{coeff} must be identical.
}

\value{
 CMM model form
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{DirectSum}}, \code{\link{SpecifyCoefficient}}, \code{\link{MarginalModelFit}}
}

\examples{
# simultaneously specify marginal independence in two marginal tables

bt1 = ConstraintMatrix(c("A","B"),list(c("A"),c("B")),c(3,3))
at1 = MarginalMatrix(c("A","B","C"),c("A","B"),c(3,3,3))
model1 = list(bt1,"log",at1)

bt2 = ConstraintMatrix(c("B","C"),list(c("B"),c("C")),c(3,3))
at2 = MarginalMatrix(c("A","B","C"),c("B","C"),c(3,3,3))
model2 = list(bt2,"log",at2)

model12 = JoinModels(model1,model2)

# the model can be fitted to an artificial data set
n = c(1:27)
fit=MarginalModelFit(n,model12)
}
\keyword{univar}
