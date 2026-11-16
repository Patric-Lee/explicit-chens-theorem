import PlattPointSubsetKernel
import PlattPointPackets.S3B000148
import PlattPointPackets.S3B000149
import PlattPointPackets.S3B000150
import PlattPointPackets.S3B000151
import PlattPointPackets.S3B000152
import PlattPointPackets.S3B000153
import PlattPointPackets.S3B000154
import PlattGlobalGrid.S7B000094
namespace ChenEffective.PlattWindow.PointCovers.S7B000094
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000148.points ++ ChenEffective.PlattWindow.PointPackets.S3B000149.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000152.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000153.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000154.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000094.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000094.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000094
