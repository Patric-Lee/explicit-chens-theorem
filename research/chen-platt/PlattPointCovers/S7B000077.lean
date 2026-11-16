import PlattPointSubsetKernel
import PlattPointPackets.S3B000049
import PlattPointPackets.S3B000050
import PlattPointPackets.S3B000051
import PlattPointPackets.S3B000052
import PlattPointPackets.S3B000053
import PlattPointPackets.S3B000054
import PlattPointPackets.S3B000055
import PlattGlobalGrid.S7B000077
namespace ChenEffective.PlattWindow.PointCovers.S7B000077
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000049.points ++ ChenEffective.PlattWindow.PointPackets.S3B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000055.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000077.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000077.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000077
