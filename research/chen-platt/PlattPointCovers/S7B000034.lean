import PlattPointSubsetKernel
import PlattPointPackets.S2B000164
import PlattPointPackets.S2B000165
import PlattPointPackets.S2B000166
import PlattPointPackets.S2B000167
import PlattPointPackets.S2B000168
import PlattGlobalGrid.S7B000034
namespace ChenEffective.PlattWindow.PointCovers.S7B000034
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000164.points ++ ChenEffective.PlattWindow.PointPackets.S2B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000168.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000034.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000034.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000034
