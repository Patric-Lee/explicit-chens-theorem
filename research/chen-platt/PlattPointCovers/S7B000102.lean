import PlattPointSubsetKernel
import PlattPointPackets.S3B000200
import PlattPointPackets.S3B000201
import PlattPointPackets.S3B000202
import PlattPointPackets.S3B000203
import PlattPointPackets.S3B000204
import PlattPointPackets.S3B000205
import PlattPointPackets.S3B000206
import PlattGlobalGrid.S7B000102
namespace ChenEffective.PlattWindow.PointCovers.S7B000102
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000200.points ++ ChenEffective.PlattWindow.PointPackets.S3B000201.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000202.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000203.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000204.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000206.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000102.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000102.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000102
