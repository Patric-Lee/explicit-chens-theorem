import PlattPointSubsetKernel
import PlattPointPackets.S2B000015
import PlattPointPackets.S2B000016
import PlattPointPackets.S2B000017
import PlattPointPackets.S2B000018
import PlattGlobalGrid.S6B000105
namespace ChenEffective.PlattWindow.PointCovers.S6B000105
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000015.points ++ ChenEffective.PlattWindow.PointPackets.S2B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000018.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000105.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000105.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000105
