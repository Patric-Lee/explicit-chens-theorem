import PlattPointSubsetKernel
import PlattPointPackets.S3B000142
import PlattPointPackets.S3B000143
import PlattPointPackets.S3B000144
import PlattPointPackets.S3B000145
import PlattPointPackets.S3B000146
import PlattPointPackets.S3B000147
import PlattPointPackets.S3B000148
import PlattGlobalGrid.S7B000093
namespace ChenEffective.PlattWindow.PointCovers.S7B000093
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000142.points ++ ChenEffective.PlattWindow.PointPackets.S3B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000148.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000093.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000093.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000093
