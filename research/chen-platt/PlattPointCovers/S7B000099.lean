import PlattPointSubsetKernel
import PlattPointPackets.S3B000180
import PlattPointPackets.S3B000181
import PlattPointPackets.S3B000182
import PlattPointPackets.S3B000183
import PlattPointPackets.S3B000184
import PlattPointPackets.S3B000185
import PlattPointPackets.S3B000186
import PlattGlobalGrid.S7B000099
namespace ChenEffective.PlattWindow.PointCovers.S7B000099
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000180.points ++ ChenEffective.PlattWindow.PointPackets.S3B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000184.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000185.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000186.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000099.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000099.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000099
