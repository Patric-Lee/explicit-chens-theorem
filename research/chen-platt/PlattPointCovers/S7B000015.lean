import PlattPointSubsetKernel
import PlattPointPackets.S2B000096
import PlattPointPackets.S2B000097
import PlattPointPackets.S2B000098
import PlattPointPackets.S2B000099
import PlattGlobalGrid.S7B000015
namespace ChenEffective.PlattWindow.PointCovers.S7B000015
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000096.points ++ ChenEffective.PlattWindow.PointPackets.S2B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000099.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000015.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000015.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000015
