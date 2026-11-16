import PlattPointSubsetKernel
import PlattPointPackets.S3B000124
import PlattPointPackets.S3B000125
import PlattPointPackets.S3B000126
import PlattPointPackets.S3B000127
import PlattPointPackets.S3B000128
import PlattPointPackets.S3B000129
import PlattPointPackets.S3B000130
import PlattGlobalGrid.S7B000090
namespace ChenEffective.PlattWindow.PointCovers.S7B000090
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000124.points ++ ChenEffective.PlattWindow.PointPackets.S3B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000130.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000090.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000090.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000090
