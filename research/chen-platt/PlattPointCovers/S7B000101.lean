import PlattPointSubsetKernel
import PlattPointPackets.S3B000193
import PlattPointPackets.S3B000194
import PlattPointPackets.S3B000195
import PlattPointPackets.S3B000196
import PlattPointPackets.S3B000197
import PlattPointPackets.S3B000198
import PlattPointPackets.S3B000199
import PlattPointPackets.S3B000200
import PlattGlobalGrid.S7B000101
namespace ChenEffective.PlattWindow.PointCovers.S7B000101
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S3B000193.points ++ ChenEffective.PlattWindow.PointPackets.S3B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000200.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000101.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000101.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000101
