import PlattPointSubsetKernel
import PlattPointPackets.S3B000118
import PlattPointPackets.S3B000119
import PlattPointPackets.S3B000120
import PlattPointPackets.S3B000121
import PlattPointPackets.S3B000122
import PlattPointPackets.S3B000123
import PlattPointPackets.S3B000124
import PlattGlobalGrid.S7B000089
namespace ChenEffective.PlattWindow.PointCovers.S7B000089
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000118.points ++ ChenEffective.PlattWindow.PointPackets.S3B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000124.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000089.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000089.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000089
