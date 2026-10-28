import WidthFixtures

namespace WidthReverse
open GeneralVE.Complexity
#eval [(maxWidth (List.finRange 16).reverse (WidthFixtures.hubScopes 16)),
    totalRows (List.finRange 16).reverse (WidthFixtures.hubScopes 16)]
#eval [(maxWidth (List.finRange 64).reverse (WidthFixtures.hubScopes 64)),
    totalRows (List.finRange 64).reverse (WidthFixtures.hubScopes 64)]
end WidthReverse
