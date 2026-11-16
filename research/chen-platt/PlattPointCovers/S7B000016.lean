import PlattPointSubsetKernel
import PlattPointPackets.S2B000099
import PlattPointPackets.S2B000100
import PlattPointPackets.S2B000101
import PlattPointPackets.S2B000102
import PlattPointPackets.S2B000103
import PlattGlobalGrid.S7B000016
namespace ChenEffective.PlattWindow.PointCovers.S7B000016
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000099.points ++ ChenEffective.PlattWindow.PointPackets.S2B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000103.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000016.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000016.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000016
