import PlattPointSubsetKernel
import PlattPointPackets.S2B000067
import PlattPointPackets.S2B000068
import PlattPointPackets.S2B000069
import PlattPointPackets.S2B000070
import PlattGlobalGrid.S7B000006
namespace ChenEffective.PlattWindow.PointCovers.S7B000006
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000067.points ++ ChenEffective.PlattWindow.PointPackets.S2B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000070.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000006.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000006.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000006
