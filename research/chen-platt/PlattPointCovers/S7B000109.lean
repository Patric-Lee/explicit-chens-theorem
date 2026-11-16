import PlattPointSubsetKernel
import PlattPointPackets.S3B000247
import PlattPointPackets.S3B000248
import PlattPointPackets.S3B000249
import PlattPointPackets.S3B000250
import PlattPointPackets.S3B000251
import PlattPointPackets.S3B000252
import PlattPointPackets.S3B000253
import PlattPointPackets.S3B000254
import PlattGlobalGrid.S7B000109
namespace ChenEffective.PlattWindow.PointCovers.S7B000109
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000247.points ++ ChenEffective.PlattWindow.PointPackets.S3B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000249.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000252.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000254.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000109.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000109.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000109
