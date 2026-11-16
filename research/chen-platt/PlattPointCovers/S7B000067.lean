import PlattPointSubsetKernel
import PlattPointPackets.S2B000309
import PlattPointPackets.S2B000310
import PlattPointPackets.S2B000311
import PlattPointPackets.S2B000312
import PlattPointPackets.S3B000000
import PlattPointPackets.S3B000001
import PlattPointPackets.S3B000002
import PlattGlobalGrid.S7B000067
namespace ChenEffective.PlattWindow.PointCovers.S7B000067
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S2B000309.points ++ ChenEffective.PlattWindow.PointPackets.S2B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000002.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000067.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000067.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000067
